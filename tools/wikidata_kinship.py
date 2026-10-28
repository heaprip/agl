#!/usr/bin/env python3
"""Loader: kinship snapshot around Queen Victoria (Q9439) from Wikidata (CC0).
The only place that touches the network. Plan: local/experiments/mini-agl/skeleton-real-plan.md.

usage: wikidata_kinship.py [OUTDIR]   (default data/wikidata)
Writes OUTDIR/kinship-victoria.tsv   rows: prop<TAB>subject<TAB>object<TAB>source (sorted, deduplicated;
                                     source = Q id of a P248 'stated in' value or '-')
       OUTDIR/kinship-victoria-sources.tsv   Q id<TAB>English label of each source
       OUTDIR/MANIFEST               queries, caps, sha256 of both files, fetch date (date only here).
BFS from the root over P25 P22 P26 P40 P3373 in both directions; batches of 30 sorted by Q number;
stops when 2000 people or 6000 distinct (prop, subj, obj) triples are reached (checked after each batch).
Deprecated-rank statements are skipped. Python stdlib only."""
import datetime
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

ENDPOINT = "https://query.wikidata.org/sparql"
UA = "agl-research-loader/0.1 (https://github.com/heaprip/agl; kinship snapshot, polite, bounded)"
ROOT = "Q9439"
PROPS = ["P25", "P22", "P26", "P40", "P3373"]
MAX_PEOPLE = 2000
MAX_TRIPLES = 6000
BATCH = 30
PAUSE = 1.5
MAX_QUERIES = 80
RETRIES = 3

_ENT = "http://www.wikidata.org/entity/"

QUERY_OUT = """SELECT ?s ?prop ?o ?src WHERE {{
  hint:Query hint:optimizer "None" .
  VALUES ?s {{ {values} }}
  {{ {blocks} }}
  FILTER(STRSTARTS(STR(?o), "http://www.wikidata.org/entity/Q"))
  ?st wikibase:rank ?rk . FILTER(?rk != wikibase:DeprecatedRank)
  OPTIONAL {{ ?st prov:wasDerivedFrom ?ref . ?ref pr:P248 ?src }}
}}"""
QUERY_IN = QUERY_OUT.replace("VALUES ?s", "VALUES ?o")
BLOCK = '?s p:{p} ?st . ?st ps:{p} ?o . BIND("{p}" AS ?prop)'
BLOCK_IN = '?st ps:{p} ?o . ?s p:{p} ?st . BIND("{p}" AS ?prop)'
QUERY_LABELS = """SELECT ?x ?l WHERE {{
  VALUES ?x {{ {values} }}
  ?x rdfs:label ?l . FILTER(LANG(?l) = "en")
}}"""

queries_done = 0


def qnum(q):
    return int(q[1:])


def sparql(text):
    global queries_done
    if queries_done >= MAX_QUERIES:
        raise SystemExit("query budget exhausted")
    data = urllib.parse.urlencode({"query": text}).encode()
    req = urllib.request.Request(ENDPOINT, data=data, headers={
        "User-Agent": UA, "Accept": "application/sparql-results+json",
        "Content-Type": "application/x-www-form-urlencoded"})
    for attempt in range(RETRIES):
        time.sleep(PAUSE * (attempt + 1))
        try:
            queries_done += 1
            with urllib.request.urlopen(req, timeout=90) as r:
                return json.loads(r.read().decode())["results"]["bindings"]
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            print("query failed (%s), attempt %d" % (e, attempt + 1), file=sys.stderr)
    raise SystemExit("network failure")


def q_of(uri):
    return uri[len(_ENT):]


def fetch_batch(frontier):
    values = " ".join("wd:" + q for q in frontier)
    rows = []
    for tmpl, blk in ((QUERY_OUT, BLOCK), (QUERY_IN, BLOCK_IN)):
        blocks = " UNION ".join("{ " + blk.format(p=p) + " }" for p in PROPS)
        for b in sparql(tmpl.format(values=values, blocks=blocks)):
            src = q_of(b["src"]["value"]) if "src" in b and b["src"]["value"].startswith(_ENT) else "-"
            rows.append((b["prop"]["value"], q_of(b["s"]["value"]), q_of(b["o"]["value"]), src))
    return rows


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else "data/wikidata"
    os.makedirs(out, exist_ok=True)
    order = [ROOT]
    seen = {ROOT}
    expanded = set()
    rows = set()
    triples = set()
    stop = False
    while not stop:
        frontier = sorted((q for q in order if q not in expanded), key=qnum)
        if not frontier:
            break
        # one level at a time: only people known at level start; new people wait for the next round
        for i in range(0, len(frontier), BATCH):
            batch = frontier[i:i + BATCH]
            for r in fetch_batch(batch):
                rows.add(r)
                triples.add(r[:3])
            expanded.update(batch)
            new = sorted({x for r in rows for x in r[1:3]} - seen, key=qnum)
            for x in new:
                seen.add(x)
                order.append(x)
            if len(order) >= MAX_PEOPLE or len(triples) >= MAX_TRIPLES or queries_done + 3 > MAX_QUERIES:
                stop = True
                print("stop: people %d triples %d queries %d" % (len(order), len(triples), queries_done),
                      file=sys.stderr)
                break
        print("people %d triples %d queries %d" % (len(order), len(triples), queries_done), file=sys.stderr)
    people = set(order[:MAX_PEOPLE])
    keep = sorted(r for r in rows if r[1] in people and r[2] in people)
    srcs = sorted({r[3] for r in keep if r[3] != "-"}, key=qnum)
    labels = {}
    for i in range(0, len(srcs), 100):
        chunk = srcs[i:i + 100]
        for b in sparql(QUERY_LABELS.format(values=" ".join("wd:" + q for q in chunk))):
            labels[q_of(b["x"]["value"])] = b["l"]["value"].replace("\t", " ").replace("\n", " ")
    snap = os.path.join(out, "kinship-victoria.tsv")
    with open(snap, "w") as f:
        for r in keep:
            f.write("\t".join(r) + "\n")
    spath = os.path.join(out, "kinship-victoria-sources.tsv")
    with open(spath, "w") as f:
        for q in srcs:
            f.write("%s\t%s\n" % (q, labels.get(q, "")))

    def sha(p):
        return hashlib.sha256(open(p, "rb").read()).hexdigest()

    with open(os.path.join(out, "MANIFEST"), "w") as f:
        f.write("source: Wikidata Query Service %s\n" % ENDPOINT)
        f.write("licence: Wikidata structured data is CC0 1.0 (public domain dedication)\n")
        f.write("root: %s  props: %s  both directions\n" % (ROOT, " ".join(PROPS)))
        f.write("caps: people<=%d  triples<=%d (checked after each batch of %d, ties by Q number)\n"
                % (MAX_PEOPLE, MAX_TRIPLES, BATCH))
        f.write("rows: %d  people: %d  distinct triples: %d  sources(P248): %d  queries: %d\n"
                % (len(keep), len(people), len({r[:3] for r in keep}), len(srcs), queries_done))
        f.write("fetched: %s (date only here; the snapshot below is the reproducible object)\n"
                % datetime.date.today().isoformat())
        f.write("sha256 kinship-victoria.tsv %s\n" % sha(snap))
        f.write("sha256 kinship-victoria-sources.tsv %s\n" % sha(spath))
        f.write("--- query template, outgoing (VALUES ?s) ---\n")
        f.write(QUERY_OUT.format(values="wd:Q..., ...", blocks=" UNION ".join(
            "{ " + BLOCK.format(p=p) + " }" for p in PROPS)) + "\n")
        f.write("--- query template, incoming (VALUES ?o; pattern order reversed so ?o is bound first) ---\n")
        f.write(QUERY_IN.format(values="wd:Q..., ...", blocks=" UNION ".join(
            "{ " + BLOCK_IN.format(p=p) + " }" for p in PROPS)) + "\n")
        f.write("--- label query ---\n" + QUERY_LABELS.format(values="wd:Q..., ...") + "\n")


if __name__ == "__main__":
    main()

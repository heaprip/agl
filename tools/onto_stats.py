#!/usr/bin/env python3
"""Shape of real ontologies, for choosing how labels with order and nesting
should be designed (docs/hypotheses.md, H61).

    tools/onto_stats.py fetch   download pinned ChEBI-lite releases into data/onto/raw/
                                and write data/onto/MANIFEST
    tools/onto_stats.py stats   offline: check MANIFEST, print the measurements

What is measured, as distributions (percentiles), not means:
  - parents per term (is_a), and roles per term (has_role: a second axis);
  - depth: shortest and longest is_a path to a root; the number of
    distinct paths (one path label each); intervals per term in the
    tree-plus-exceptions labelling of Agrawal, Borgida, Jagadish (1989);
  - children per internal node (branching);
  - between releases, for terms present in both: whether the direct parents
    stayed, gained a new intermediate level (an old parent is now an
    ancestor of a new parent), gained an extra parent, or moved elsewhere;
    and how many terms changed their set of ancestors at all (each such term
    would change a path label).

Data: ChEBI, CC BY 4.0, https://www.ebi.ac.uk/chebi/. Releases 200 (June
2021) and 244 (August 2025) are ChEBI 1.0; 255 (September 2026) is ChEBI 2.0,
so the 244 → 255 comparison crosses a change of system.

Standard library only. Only `fetch` touches the network.
"""

import gzip
import hashlib
import pathlib
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
RAW = ROOT / "data" / "onto" / "raw"
MANIFEST = ROOT / "data" / "onto" / "MANIFEST"
ARCHIVE = "https://ftp.ebi.ac.uk/pub/databases/chebi/archive"
RELEASES = {
    "200": f"{ARCHIVE}/chebi_legacy/archive/rel200/ontology/chebi_lite.obo.gz",
    "244": f"{ARCHIVE}/chebi_legacy/archive/rel244/ontology/chebi_lite.obo.gz",
    "255": f"{ARCHIVE}/rel255/ontology/chebi_lite.obo.gz",
}


def fetch():
    RAW.mkdir(parents=True, exist_ok=True)
    for rel, url in RELEASES.items():
        path = RAW / f"chebi_lite_{rel}.obo.gz"
        if not path.exists():
            with urllib.request.urlopen(url, timeout=300) as r:
                path.write_bytes(r.read())
    files = sorted(p for p in RAW.iterdir() if p.is_file())
    MANIFEST.write_text("".join(
        f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.name}\n" for p in files))
    print(f"{len(files)} raw files")


def verified():
    for line in MANIFEST.read_text().splitlines():
        digest, name = line.split("  ", 1)
        if hashlib.sha256((RAW / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"{name}: content does not match MANIFEST")


def load(rel):
    """Terms of a release: id -> (is_a parents, has_role targets); obsolete terms dropped."""
    terms = {}
    cur = None
    with gzip.open(RAW / f"chebi_lite_{rel}.obo.gz", "rt", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line.startswith("["):
                cur = None
                if line == "[Term]":
                    cur = {"id": None, "name": None, "is_a": set(), "role": set(), "obsolete": False}
                    terms_list.append(cur)
                continue
            if cur is None or ":" not in line:
                continue
            key, val = line.split(":", 1)
            val = val.split("!")[0].strip()
            if key == "id":
                cur["id"] = val
            elif key == "name":
                cur["name"] = val
            elif key == "is_a":
                cur["is_a"].add(val.split()[0])
            elif key == "relationship" and val.split()[0] in ("has_role", "RO:0000087"):
                cur["role"].add(val.split()[1])
            elif key == "is_obsolete" and val == "true":
                cur["obsolete"] = True
    for t in terms_list:
        # ChEBI 2.0 writes merged ids as stanzas with only `id` and `alt_id`.
        if t["id"] and t["name"] and not t["obsolete"]:
            terms[t["id"]] = (t["is_a"], t["role"])
    terms_list.clear()
    # Parents that are not live terms (obsolete or outside the file) are dropped.
    return {k: ({p for p in pa if p in terms}, ro) for k, (pa, ro) in terms.items()}


terms_list = []


def pct(xs, ps=(50, 90, 99)):
    xs = sorted(xs)
    if not xs:
        return "—"
    out = [f"p{p} {xs[min(len(xs) - 1, len(xs) * p // 100)]}" for p in ps]
    return ", ".join(out) + f", max {xs[-1]} (n {len(xs)})"


def depths(parents):
    """Shortest and longest is_a path to a root, by memoized recursion in id order."""
    short, long_ = {}, {}
    sys.setrecursionlimit(100000)

    def go(t):
        if t in short:
            return
        ps = sorted(parents[t])
        if not ps:
            short[t] = long_[t] = 0
            return
        short[t] = long_[t] = None  # cycle guard
        for p in ps:
            go(p)
        ok = [p for p in ps if short[p] is not None]
        short[t] = 1 + min(short[p] for p in ok) if ok else 0
        long_[t] = 1 + max(long_[p] for p in ok) if ok else 0

    for t in sorted(parents):
        go(t)
    return short, long_


def paths(parents):
    """Number of distinct is_a paths from a term to a root: one path label each."""
    memo = {}

    def go(t):
        if t not in memo:
            memo[t] = 1  # cycle guard
            ps = parents[t]
            memo[t] = sum(go(p) for p in sorted(ps)) if ps else 1
        return memo[t]

    for t in sorted(parents):
        go(t)
    return memo


def intervals(parents):
    """Interval labels for reachability in a DAG (Agrawal, Borgida, Jagadish,
    1989): a spanning tree (each term keeps its smallest-id parent) numbered
    in post-order; a term is labelled by its number, and an ancestor keeps
    the merged intervals of everything below it. Returns intervals per term."""
    kids = {}
    for t in sorted(parents):
        ps = sorted(parents[t])
        if ps:
            kids.setdefault(ps[0], []).append(t)
    post, low = {}, {}
    n = 0
    for root in sorted(t for t in parents if not parents[t]):
        stack = [(root, False)]
        while stack:
            t, done = stack.pop()
            if done:
                low[t] = min(low[c] for c in kids[t]) if kids.get(t) else n
                post[t] = n
                n += 1
            else:
                stack.append((t, True))
                for c in reversed(kids.get(t, [])):
                    stack.append((c, False))
    children = {}
    for t in sorted(parents):
        for p in parents[t]:
            children.setdefault(p, []).append(t)
    memo = {}
    order = sorted(post, key=lambda t: post[t])
    sys.setrecursionlimit(100000)

    def go(t):
        if t in memo:
            return memo[t]
        memo[t] = [(low[t], post[t])]  # cycle guard
        iv = [(low[t], post[t])]
        for c in children.get(t, []):
            iv += go(c)
        iv.sort()
        merged = []
        for a, b in iv:
            if merged and a <= merged[-1][1] + 1:
                merged[-1] = (merged[-1][0], max(merged[-1][1], b))
            else:
                merged.append((a, b))
        memo[t] = merged
        return merged

    for t in order:
        go(t)
    return {t: len(v) for t, v in memo.items()}


def ancestors(parents):
    memo = {}

    def go(t):
        if t not in memo:
            memo[t] = set()  # cycle guard
            acc = set()
            for p in parents[t]:
                acc.add(p)
                acc |= go(p)
            memo[t] = acc
        return memo[t]

    for t in sorted(parents):
        go(t)
    return memo


def shape(rel):
    terms = load(rel)
    parents = {k: v[0] for k, v in terms.items()}
    children = {}
    for k, ps in parents.items():
        for p in ps:
            children[p] = children.get(p, 0) + 1
    short, long_ = depths(parents)
    anc = ancestors(parents)
    n = len(terms)
    multi = sum(len(ps) >= 2 for ps in parents.values())
    roles = [len(v[1]) for v in terms.values()]
    print(f"== release {rel}: {n} terms, roots {sum(not ps for ps in parents.values())}")
    print(f"  parents (is_a): {pct([len(p) for p in parents.values()])}; with >= 2: {multi} ({100 * multi / n:.1f}%)")
    print(f"  roles (has_role): {pct(roles)}; with any: {sum(r > 0 for r in roles)}")
    print(f"  depth, shortest path: {pct(list(short.values()))}")
    print(f"  depth, longest path: {pct(list(long_.values()))}")
    print(f"  longest minus shortest: {pct([long_[t] - short[t] for t in terms])}")
    print(f"  ancestors: {pct([len(a) for a in anc.values()])}")
    print(f"  distinct paths to a root: {pct(list(paths(parents).values()))}")
    iv = intervals(parents)
    print(f"  intervals per term (tree + exceptions): {pct(list(iv.values()))}; total {sum(iv.values())}")
    print(f"  children per internal node: {pct(list(children.values()))}")
    return parents, anc


def compare(a, b, pa, aa, pb, ab):
    both = sorted(set(pa) & set(pb))
    kinds = {"same": 0, "intermediate": 0, "extra parent": 0, "moved": 0}
    changed_anc = 0
    new_terms = set(pb) - set(pa)
    via_new = 0
    for t in both:
        old, new = pa[t], pb[t]
        if ab[t] != aa[t]:
            changed_anc += 1
        if old == new:
            kinds["same"] += 1
        elif any(o in ab[q] for o in old for q in new - old):
            kinds["intermediate"] += 1
            if any(q in new_terms for q in new - old):
                via_new += 1
        elif old <= new:
            kinds["extra parent"] += 1
        else:
            kinds["moved"] += 1
    n = len(both)
    print(f"== {a} → {b}: {n} terms in both, {len(new_terms)} new, {len(set(pa) - set(pb))} gone")
    for k, v in kinds.items():
        print(f"  direct parents {k}: {v} ({100 * v / n:.2f}%)")
    print(f"  intermediate level through a new term: {via_new}")
    print(f"  ancestor set changed (a path label would change): {changed_anc} ({100 * changed_anc / n:.2f}%)")


def stats():
    verified()
    shapes = {rel: shape(rel) for rel in RELEASES}
    rels = list(RELEASES)
    for a, b in zip(rels, rels[1:]):
        compare(a, b, *shapes[a], *shapes[b])


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "fetch":
        fetch()
    elif cmd == "stats":
        stats()
    else:
        print(__doc__)

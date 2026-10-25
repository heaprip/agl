#!/usr/bin/env python3
"""Shape of real ontologies, for choosing how labels with order and nesting
should be designed (docs/hypotheses.md, H61).

    tools/onto_stats.py fetch   download pinned releases of ChEBI-lite and Open English
                                WordNet into data/onto/raw/ and write data/onto/MANIFEST
    tools/onto_stats.py stats   offline: check MANIFEST, print the measurements
    tools/onto_stats.py edges FAMILY RELEASE
                                offline: print is_a edges as "species<TAB>genus" lines,
                                sorted (input of examples/labels.rs)
    tools/onto_stats.py probe FAMILY RELEASE lazy|whole
                                offline: print an .agl program with every is_a edge as a
                                fact, a nesting over them and 20 + 10 questions drawn from
                                seed 1 (H61, step 2b)
    tools/onto_stats.py releases FAMILY A B
                                offline: print an .agl program with two releases as two
                                planes, a lazy nesting and 80 questions from seed 1
                                (H61, step 7)
    tools/onto_stats.py axes chebi RELEASE [one]
                                offline: print an .agl program with two axes, structure
                                (is_a) and role (has_role, roles' is_a), and 50 questions
                                "has x role r" from seed 1; `one`: a single nesting for
                                both hierarchies (H61, step 4)
    tools/onto_stats.py replay  offline: lay the edits between releases onto the numbers
                                of the earlier one, for three forms of a number (H61)

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
Open English WordNet (CC BY 4.0), https://en-word.net/: editions 2019, 2021,
2025 (the "plus" build); nouns only. A genus is a hypernym or instance hypernym; the second
axis is holonymy (part, member, substance). Synset ids are compared with
the prefix (ewn-, oewn-) stripped.

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
WN = "https://github.com/globalwordnet/english-wordnet/releases/download"
# Family -> release -> (file name, url).
SOURCES = {
    "chebi": {
        "200": ("chebi_lite_200.obo.gz", f"{ARCHIVE}/chebi_legacy/archive/rel200/ontology/chebi_lite.obo.gz"),
        "244": ("chebi_lite_244.obo.gz", f"{ARCHIVE}/chebi_legacy/archive/rel244/ontology/chebi_lite.obo.gz"),
        "255": ("chebi_lite_255.obo.gz", f"{ARCHIVE}/rel255/ontology/chebi_lite.obo.gz"),
    },
    # The 2025 edition without "plus" leaves out instances (proper nouns) and
    # one direction of meronymy; "plus" is comparable with earlier editions.
    "wordnet": {
        y: (f"english-wordnet-{f}.xml.gz", f"{WN}/{y}-edition/english-wordnet-{f}.xml.gz")
        for y, f in (("2019", "2019"), ("2021", "2021"), ("2025", "2025-plus"))
    },
}


def fetch():
    RAW.mkdir(parents=True, exist_ok=True)
    for name, url in (v for fam in SOURCES.values() for v in fam.values()):
        path = RAW / name
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


def load_chebi(name):
    """Terms of a release: id -> (is_a parents, has_role targets); obsolete terms dropped."""
    terms = {}
    cur = None
    with gzip.open(RAW / name, "rt", encoding="utf-8") as f:
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


def load_wordnet(name):
    """Noun synsets: id (prefix stripped) -> (hypernyms, holonyms)."""
    import xml.etree.ElementTree as ET

    def strip(i):
        return i.split("-", 1)[1]

    terms = {}
    with gzip.open(RAW / name) as f:
        for _, el in ET.iterparse(f):
            if el.tag != "Synset":
                continue
            if el.get("partOfSpeech") == "n":
                genus, whole = set(), set()
                for r in el.iter("SynsetRelation"):
                    t = r.get("relType")
                    if t in ("hypernym", "instance_hypernym"):
                        genus.add(strip(r.get("target")))
                    elif t in ("holo_part", "holo_member", "holo_substance"):
                        whole.add(strip(r.get("target")))
                terms[strip(el.get("id"))] = (genus, whole)
            el.clear()
    return {k: ({p for p in g if p in terms}, w) for k, (g, w) in terms.items()}


def load(family, rel):
    name = SOURCES[family][rel][0]
    return load_chebi(name) if family == "chebi" else load_wordnet(name)


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


def shape(family, rel):
    terms = load(family, rel)
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
    print(f"== {family} {rel}: {n} terms, roots {sum(not ps for ps in parents.values())}")
    print(f"  genera: {pct([len(p) for p in parents.values()])}; with >= 2: {multi} ({100 * multi / n:.1f}%)")
    print(f"  second axis (roles / wholes): {pct(roles)}; with any: {sum(r > 0 for r in roles)}")
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
    for family, releases in SOURCES.items():
        shapes = {rel: shape(family, rel) for rel in releases}
        rels = list(releases)
        for a, b in zip(rels, rels[1:]):
            compare(f"{family} {a}", b, *shapes[a], *shapes[b])


def edges(family, rel):
    verified()
    out = sorted((t, p) for t, (ps, _) in load(family, rel).items() for p in ps)
    sys.stdout.write("".join(f"{t}\t{p}\n" for t, p in out))


def probe(family, rel, kind):
    import random
    verified()
    parents = {t: sorted(ps) for t, (ps, _) in load(family, rel).items()}
    anc = ancestors(parents)
    name = lambda s: "s" + s.replace("-", "_").replace(":", "_")
    edges = sorted((t, p) for t, ps in parents.items() for p in ps)
    nodes = sorted(t for t in parents if parents[t])
    rng = random.Random(1)
    yes, no = [], []
    while len(yes) < 20:
        x = rng.choice(nodes)
        yes.append((x, rng.choice(sorted(anc[x]))))
    while len(no) < 10:
        x, y = rng.choice(nodes), rng.choice(nodes)
        if y not in anc[x] and x != y:
            no.append((x, y))
    lazy = " lazy" if kind == "lazy" else ""
    out = ["status source > question\n",
           f"nesting k: kind_of(a, b) by is_a(species, genus){lazy}\n",
           "rule found strict @: found(x: ?x, y: ?y) <- probe(x: ?x, y: ?y), kind_of(a: ?x, b: ?y)\n"]
    out += [f"fact e{i}: is_a(species: {name(a)}, genus: {name(b)}) @ [source]\n" for i, (a, b) in enumerate(edges)]
    out += [f"fact p{i}: probe(x: {name(a)}, y: {name(b)}) @ [question]\n" for i, (a, b) in enumerate(yes + no)]
    # The kernel's world is open: what is not derived is unknown, not no.
    out += [f"query found(x: {name(a)}, y: {name(b)}) @ expect yes\n" for a, b in yes]
    out += [f"query found(x: {name(a)}, y: {name(b)}) @ expect unknown\n" for a, b in no]
    sys.stdout.write("".join(out))


def sticky_tree(parents, old_tree):
    """Main genus of each term: the one it had, while it is still a genus;
    otherwise the smallest id. Terms without a genus are roots (None)."""
    tree = {}
    for t in sorted(parents):
        ps = parents[t]
        keep = old_tree.get(t)
        tree[t] = keep if keep in ps else (min(ps) if ps else None)
    return tree


def chains(tree):
    """Chain of main genera from the root down to each term: the path label."""
    memo = {}

    def go(t):
        if t not in memo:
            memo[t] = (t,)  # cycle guard
            p = tree[t]
            memo[t] = (go(p) if p is not None else ()) + (t,)
        return memo[t]

    for t in sorted(tree):
        go(t)
    return memo


def postorder(tree):
    """Post-order number of each term in the tree, children by id."""
    kids = {}
    for t in sorted(tree):
        if tree[t] is not None:
            kids.setdefault(tree[t], []).append(t)
    post, n = {}, 0
    for root in sorted(t for t in tree if tree[t] is None):
        stack = [(root, False)]
        while stack:
            t, done = stack.pop()
            if done:
                post[t] = n
                n += 1
            else:
                stack.append((t, True))
                for c in reversed(kids.get(t, [])):
                    stack.append((c, False))
    return post


def regions(parents, rank):
    """Merged intervals of ranks of each term and everything below it, for a
    given numbering (rank: term -> 0..n-1 without holes)."""
    children = {}
    for t in sorted(parents):
        for p in parents[t]:
            children.setdefault(p, []).append(t)
    memo = {}
    sys.setrecursionlimit(100000)

    def go(t):
        if t in memo:
            return memo[t]
        memo[t] = [(rank[t], rank[t])]  # cycle guard
        iv = [(rank[t], rank[t])]
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

    for t in sorted(rank, key=rank.get):
        go(t)
    return memo


def frozen_keys(keys, parents, tree):
    """Keys of form B: terms that had a key keep it; a new term goes into the
    gap just before its main genus, new siblings in id order. A key is a
    tuple compared lexicographically, so there is always room."""
    keys = dict(keys)
    top = max((k[0] for k in keys.values()), default=0) + 1
    new = sorted(t for t in parents if t not in keys)
    slot = {}

    def key(t):
        if t not in keys:
            keys[t] = ()  # cycle guard
            p = tree[t]
            base = key(p) if p is not None and key(p) != () else (top, 1)
            i = slot.get(base, 0)
            slot[base] = i + 1
            keys[t] = base[:-1] + (base[-1] - 1, i, 1)
        return keys[t]

    for t in new:
        key(t)
    return {t: keys[t] for t in parents}


def replay_family(family, rels):
    """Lay the edits of each next release onto the numbers of the previous one."""
    first = {t: ps for t, (ps, _) in load(family, rels[0]).items()}
    tree = sticky_tree(first, {})
    post = postorder(tree)
    keys = {t: (post[t], 1) for t in first}
    pa, aa = first, ancestors(first)
    print(f"== {family} {rels[0]}: {len(first)} terms")
    for rel in rels[1:]:
        pb = {t: ps for t, (ps, _) in load(family, rel).items()}
        ab = ancestors(pb)
        both = sorted(set(pa) & set(pb))
        n = len(both)
        print(f"== {family} → {rel}: {n} terms in both, {len(set(pb) - set(pa))} new")
        # A: path label with sticky main genus.
        tb = sticky_tree(pb, tree)
        ca, cb = chains(tree), chains(tb)
        own = sum(ca[t] != cb[t] and tree[t] != tb[t] for t in both)
        inherited = sum(ca[t] != cb[t] and tree[t] == tb[t] for t in both)
        print(f"  A path: number changed {own + inherited} ({100 * (own + inherited) / n:.2f}%): "
              f"own main genus {own}, an ancestor's {inherited}")
        # B: frozen numbers, intervals recomputed.
        keys = frozen_keys({t: k for t, k in keys.items() if t in pb}, pb, tb)
        rank = {t: i for i, t in enumerate(sorted(pb, key=lambda t: (keys[t], t)))}
        frozen = regions(pb, rank)
        fresh_post = postorder(tb)
        fresh = regions(pb, fresh_post)
        closure = sum(len(a) for a in ab.values())
        for name, reg in (("frozen", frozen), ("fresh", fresh)):
            covered = sum(b - a + 1 for iv in reg.values() for a, b in iv) - len(reg)
            assert covered == closure, (name, covered, closure)
        nf = sum(len(v) for v in frozen.values())
        nr = sum(len(v) for v in fresh.values())
        print(f"  B frozen: numbers changed 0; intervals {nf} vs {nr} when renumbered "
              f"({nf / nr:.2f}x); per term {pct([len(v) for v in frozen.values()])}")
        print(f"    renumbered: intervals per term {pct([len(v) for v in fresh.values()])}")
        depth = [len(k) // 2 for k in keys.values()]
        print(f"    key length (gap levels) {pct(depth)}")
        # C: bounds only, the axes are not in the data.
        low = sum(pa[t] != pb[t] for t in both)
        high = sum(aa[t] != ab[t] for t in both)
        print(f"  C axes (bounds): own coordinates {low} ({100 * low / n:.2f}%), "
              f"ancestor set {high} ({100 * high / n:.2f}%)")
        print(f"  closure {closure} pairs; checked by both labellings")
        pa, aa, tree = pb, ab, tb


def replay():
    verified()
    for family, releases in SOURCES.items():
        replay_family(family, list(releases))


def releases(family, a, b):
    import random
    verified()
    pa = {t: ps for t, (ps, _) in load(family, a).items()}
    pb = {t: ps for t, (ps, _) in load(family, b).items()}
    aa, ab = ancestors(pa), ancestors(pb)
    name = lambda s: "s" + s.replace("-", "_").replace(":", "_")
    ea = {(t, p) for t, ps in pa.items() for p in ps}
    eb = {(t, p) for t, ps in pb.items() for p in ps}
    ra, rb = f"r{a}", f"r{b}"
    # Pairs (species, ancestor) by where nesting holds, from seed 1.
    rng = random.Random(1)
    pairs = {"both": [], a: [], b: [], "none": []}
    nodes = sorted(set(pa) | set(pb))
    seen = set()
    while any(len(v) < 10 for v in pairs.values()):
        x, y = rng.choice(nodes), rng.choice(nodes)
        if rng.random() < 0.5:
            # Draw from one release's ancestors, or nesting would be rare.
            src = aa if rng.random() < 0.5 else ab
            if not src.get(x):
                continue
            y = rng.choice(sorted(src[x]))
        if x == y or (x, y) in seen:
            continue
        seen.add((x, y))
        ia, ib = y in aa.get(x, ()), y in ab.get(x, ())
        kind = "both" if ia and ib else a if ia else b if ib else "none"
        if len(pairs[kind]) < 10:
            pairs[kind].append((x, y))
    asked = [xy for k in ("both", a, b, "none") for xy in pairs[k]]
    out = ["status source > question\n",
           f"axis release\nvalue release {family}\n",
           f"value release {ra} in {family}\nvalue release {rb} in {family}\n",
           f"plane {ra} = release:{ra}\nplane {rb} = release:{rb}\n",
           "nesting k: kind_of(a, b) by is_a(species, genus) lazy\n",
           "rule found strict @: found(x: ?x, y: ?y) <- probe(x: ?x, y: ?y), kind_of(a: ?x, b: ?y)\n"]
    for i, (t, p) in enumerate(sorted(ea | eb)):
        where = f"release:{family}" if (t, p) in ea and (t, p) in eb else ra if (t, p) in ea else rb
        out.append(f"fact e{i}: is_a(species: {name(t)}, genus: {name(p)}) @ {where} [source]\n")
    out += [f"fact p{i}: probe(x: {name(x)}, y: {name(y)}) @ [question]\n" for i, (x, y) in enumerate(asked)]
    for x, y in asked:
        for plane, anc in ((ra, aa), (rb, ab)):
            want = "yes" if y in anc.get(x, ()) else "unknown"
            out.append(f"query found(x: {name(x)}, y: {name(y)}) @ {plane} expect {want}\n")
    sys.stdout.write("".join(out))


ROLE = "CHEBI:50906"


def axes(rel, one):
    """Roles are inherited down the structure and up the roles: x has role r
    when x or an ancestor has_role r or a species of r."""
    import random
    verified()
    terms = load("chebi", rel)
    parents = {t: ps for t, (ps, _) in terms.items()}
    anc = ancestors(parents)
    roles = {t for t in terms if t == ROLE or ROLE in anc[t]}
    has = {t: hr for t, (_, hr) in terms.items() if hr}
    name = lambda s: "s" + s.replace("-", "_").replace(":", "_")

    def kinds(x):
        """Roles of x by the shortest way they come: own, down, up, both."""
        own = set(has.get(x, ()))
        down = {r for y in anc[x] for r in has.get(y, ())} - own
        up = {q for r in own for q in anc[r]} - own - down
        every = {q for y in {x} | anc[x] for r in has.get(y, ()) for q in {r} | anc[r]}
        both = every - own - down - up
        return {"own": own, "down": down, "up": up, "both": both}, every

    rng = random.Random(1)
    chem = sorted(t for t in terms if t not in roles)
    rlist = sorted(roles)
    want = {"own": [], "down": [], "up": [], "both": [], "none": []}
    while any(len(v) < 10 for v in want.values()):
        x = rng.choice(chem)
        ks, every = kinds(x)
        for k in ("own", "down", "up", "both"):
            if len(want[k]) < 10 and ks[k] and rng.random() < 0.5:
                want[k].append((x, rng.choice(sorted(ks[k]))))
        if len(want["none"]) < 10 and rng.random() < 0.2:
            r = rng.choice(rlist)
            if r not in every:
                want["none"].append((x, r))
    asked = [xr for k in want for xr in want[k]]
    rk = "kind_of" if one else "role_kind"
    out = ["status source > question\n",
           "nesting k: kind_of(a, b) by is_a(species, genus) lazy\n"]
    if not one:
        out.append("nesting kr: role_kind(a, b) by role_is_a(species, genus) lazy\n")
    p = "probe(x: ?x, r: ?r)"
    out += [f"rule own strict @: has(x: ?x, r: ?r) <- {p}, has_role(x: ?x, role: ?r)\n",
            f"rule down strict @: has(x: ?x, r: ?r) <- {p}, kind_of(a: ?x, b: ?y), has_role(x: ?y, role: ?r)\n",
            f"rule up strict @: has(x: ?x, r: ?r) <- {p}, has_role(x: ?x, role: ?q), {rk}(a: ?q, b: ?r)\n",
            f"rule both strict @: has(x: ?x, r: ?r) <- {p}, kind_of(a: ?x, b: ?y), "
            f"has_role(x: ?y, role: ?q), {rk}(a: ?q, b: ?r)\n"]
    edges = sorted((t, g) for t, ps in parents.items() for g in ps)
    for i, (t, g) in enumerate(edges):
        e = "role_is_a" if t in roles and not one else "is_a"
        out.append(f"fact e{i}: {e}(species: {name(t)}, genus: {name(g)}) @ [source]\n")
    hr = sorted((t, r) for t, rs in has.items() for r in rs)
    out += [f"fact h{i}: has_role(x: {name(t)}, role: {name(r)}) @ [source]\n" for i, (t, r) in enumerate(hr)]
    out += [f"fact p{i}: probe(x: {name(x)}, r: {name(r)}) @ [question]\n" for i, (x, r) in enumerate(asked)]
    for k, xs in want.items():
        for x, r in xs:
            out.append(f"query has(x: {name(x)}, r: {name(r)}) @ expect {'unknown' if k == 'none' else 'yes'}  # {k}\n")
    sys.stdout.write("".join(out))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "fetch":
        fetch()
    elif cmd == "stats":
        stats()
    elif cmd == "edges":
        edges(sys.argv[2], sys.argv[3])
    elif cmd == "probe":
        probe(sys.argv[2], sys.argv[3], sys.argv[4])
    elif cmd == "releases":
        releases(sys.argv[2], sys.argv[3], sys.argv[4])
    elif cmd == "axes":
        axes(sys.argv[2], sys.argv[3:] == ["one"])
    elif cmd == "replay":
        replay()
    else:
        print(__doc__)

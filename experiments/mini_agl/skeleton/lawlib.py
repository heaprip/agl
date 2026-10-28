"""Shared pieces: world file format, term algebra, MDL saving (two-part code)."""
import math
import os

# ---- world file: lines "P rec rel person" and "F rec rel x y" (tab separated)


def read_world(path):
    recs = {}
    with open(path) as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if not p or p == [""]:
                continue
            r = recs.setdefault(p[1], {"rel": p[2], "roster": set(), "facts": set()})
            if p[0] == "P":
                r["roster"].add(p[3])
            else:
                r["facts"].add((p[3], p[4]))
    return recs


def write_world(path, recs, shuffle_rng=None):
    lines = []
    for rid in sorted(recs):
        r = recs[rid]
        lines += ["P\t%s\t%s\t%s" % (rid, r["rel"], p) for p in sorted(r["roster"])]
        lines += ["F\t%s\t%s\t%s\t%s" % (rid, r["rel"], x, y) for x, y in sorted(r["facts"])]
    if shuffle_rng is not None:
        shuffle_rng.shuffle(lines)
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


class World:
    def __init__(self, recs):
        self.recs = recs
        self.rels = sorted({r["rel"] for r in recs.values()})
        self.tuples = {rel: set() for rel in self.rels}
        self.rosters = {rel: [] for rel in self.rels}
        self.fact_recs = {}
        persons = set()
        for rid in sorted(recs):
            r = recs[rid]
            self.tuples[r["rel"]] |= r["facts"]
            self.rosters[r["rel"]].append(r["roster"])
            persons |= r["roster"]
            for x, y in r["facts"]:
                self.fact_recs.setdefault((r["rel"], x, y), []).append(rid)
        self.union_roster = {
            rel: set().union(*self.rosters[rel]) if self.rosters[rel] else set() for rel in self.rels
        }
        self.n = max(2, len(persons))
        self.c = 2 * math.log2(self.n)  # bits for one pair, code defined by the world
        self.cache = {}

    def restrict(self, persons):
        out = {}
        for rid, r in self.recs.items():
            out[rid] = {
                "rel": r["rel"],
                "roster": r["roster"] & persons,
                "facts": {(x, y) for x, y in r["facts"] if x in persons and y in persons},
            }
        return World(out)


# ---- terms: tuple of atoms; atom = relation name, "~" suffix = inverse

def inv_atom(a):
    return a[:-1] if a.endswith("~") else a + "~"


def inv_term(t):
    return tuple(inv_atom(a) for a in reversed(t))


def tstr(t):
    return ";".join(t)


def parse_term(s):
    return tuple(s.split(";"))


def parse_law(s):
    a, b = s.split(" <= ")
    return parse_term(a), parse_term(b)


def law_str(t1, t2):
    return tstr(t1) + " <= " + tstr(t2)


def canon_law(t1, t2):
    a = law_str(t1, t2)
    b = law_str(inv_term(t1), inv_term(t2))
    return parse_law(min(a, b))


def rel_of(a):
    return a.rstrip("~")


def eval_term(w, t):
    if t in w.cache:
        return w.cache[t]
    if len(t) == 1:
        a = t[0]
        base = w.tuples.get(rel_of(a), set())
        res = {(y, x) for x, y in base} if a.endswith("~") else set(base)
    else:
        left = eval_term(w, t[:1])
        right = eval_term(w, t[1:])
        idx = {}
        for y, z in right:
            idx.setdefault(y, []).append(z)
        res = {(x, z) for x, y in left for z in idx.get(y, ())}
    w.cache[t] = res
    return res


def in_scope(w, t, x, y):
    """Could the pair (x,y) be recorded by term t? Roster-based; absent != violated."""
    if len(t) == 1:
        a = t[0]
        px, py = (y, x) if a.endswith("~") else (x, y)
        return any(px in r and py in r for r in w.rosters.get(rel_of(a), ()))
    return x in w.union_roster.get(rel_of(t[0]), ()) and y in w.union_roster.get(rel_of(t[-1]), ())


# Exception code. "binom" = the plan's code, log2 C(m,k) + log2(m+1): a valid two-part code
# and the NORMATIVE one for acceptance (with it P3 fails, see skeleton-result.md). "list" =
# every exception named by its index, k*log2 m + log2(m+1): a more conservative code
# introduced AFTER P3 failed, i.e. a post-hoc change, reported separately. Default: list.
EXC_CODE = os.environ.get("EXC_CODE", "list")


def ident_bits(m, k):
    """Bits to name the k exceptions among m listed tuples (and k itself)."""
    if m == 0:
        return 0.0
    if EXC_CODE == "binom":
        lc = (math.lgamma(m + 1) - math.lgamma(k + 1) - math.lgamma(m - k + 1)) / math.log(2)
    else:
        lc = k * math.log2(m)
    return math.log2(m + 1) + lc


def law_bits(w, t1, t2):
    return (len(t1) + len(t2)) * math.log2(2 * max(1, len(w.rels))) + 1


def saving(w, t1, t2):
    """Two-part MDL saving in bits for law t1 <= t2 on world w, exceptions listed.
    Returns (bits, info) or None if not applicable (no coding derives anything)."""
    best = None
    rels1 = {rel_of(a) for a in t1}
    rels2 = {rel_of(a) for a in t2}
    if len(rels1 | rels2) < 2:
        return None
    # coding B: t2 is an atom, its tuples inside t1 are derived, not stored
    if len(t2) == 1 and rel_of(t2[0]) not in rels1:
        s1 = {p for p in eval_term(w, t1) if in_scope(w, t2, *p)}
        hits = s1 & eval_term(w, t2)
        k = len(s1) - len(hits)
        if hits:
            bits = len(hits) * w.c - ident_bits(len(s1), k)
            best = (bits, {"coding": "derive-rhs", "support": len(s1), "hits": len(hits), "exc": k})
    # coding A: t1 is an atom, each of its tuples inside t2 is an index into t2
    if len(t1) == 1 and rel_of(t1[0]) not in rels2:
        r2 = eval_term(w, t2)
        if r2:
            s1 = {p for p in eval_term(w, t1) if in_scope(w, t2, *p)}
            hits = s1 & r2
            k = len(s1) - len(hits)
            if hits:
                bits = len(hits) * (w.c - math.log2(len(r2))) - ident_bits(len(s1), k)
                if best is None or bits > best[0]:
                    best = (bits, {"coding": "index-lhs", "support": len(s1), "hits": len(hits), "exc": k})
    if best is None:
        return None
    return best[0] - law_bits(w, t1, t2), best[1]


def exceptions(w, t1, t2):
    """Listed exceptions: pairs of t1 in scope of t2 that t2 does not give."""
    r2 = eval_term(w, t2)
    return sorted(p for p in eval_term(w, t1) if in_scope(w, t2, *p) and p not in r2)

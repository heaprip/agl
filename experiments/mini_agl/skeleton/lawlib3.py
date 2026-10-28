"""v3 pieces (plan skeleton-v3-plan.md): conditions (one extra atom on a variable of the law) and the
law restricted to the plane they define, evaluated with the same two-part MDL machinery as lawlib.

A condition is (var, role, rel): variable `var` (0 = x, 1 = y of a pair of the law's left term) occurs as
the first (role 0) / second (role 1) argument of relation `rel` in some record of the evaluated world.
None = empty condition = universal plane."""
import math

from lawlib import eval_term, ident_bits, in_scope, law_bits, rel_of, saving

RELS = ["father", "mother", "partner", "raised_by"]
CONDS = [(v, r, rel) for v in (0, 1) for r in (0, 1) for rel in RELS]  # 16, fixed order
COND_BITS = math.log2(len(CONDS))
MIN_PLANE = 10
HIGH = 1 / 3


def cond_name(c):
    return "-" if c is None else "%s:%s(%s)" % ("xy"[c[0]], ("1st", "2nd")[c[1]], c[2])


def parse_cond(s):
    if s == "-":
        return None
    v, rest = s.split(":")
    role, rel = rest[:-1].split("(")
    return ("xy".index(v), ("1st", "2nd").index(role), rel)


def members(w, c):
    """Persons occurring in role c[1] of relation c[2] in some record of w."""
    cache = w.__dict__.setdefault("ccache", {})
    key = (c[1], c[2])
    if key not in cache:
        cache[key] = {t[c[1]] for t in w.tuples.get(c[2], ())}
    return cache[key]


def keep_fn(w, c):
    if c is None:
        return lambda p: True
    m = members(w, c)
    v = c[0]
    return lambda p: p[v] in m


def domain(w, t1, t2, c=None):
    """Pairs of t1 in scope of t2 that satisfy condition c (the plane's part of the law's domain)."""
    keep = keep_fn(w, c)
    return {p for p in eval_term(w, t1) if in_scope(w, t2, *p) and keep(p)}


def saving_c(w, t1, t2, c=None):
    """Two-part MDL saving of the law restricted to the plane of condition c; same codings as lawlib.saving.
    Returns (bits, info) or None."""
    if c is None:
        return saving(w, t1, t2)
    keep = keep_fn(w, c)
    best = None
    rels1 = {rel_of(a) for a in t1}
    rels2 = {rel_of(a) for a in t2}
    if len(rels1 | rels2) < 2:
        return None
    if len(t2) == 1 and rel_of(t2[0]) not in rels1:
        s1 = {p for p in eval_term(w, t1) if keep(p) and in_scope(w, t2, *p)}
        hits = s1 & eval_term(w, t2)
        k = len(s1) - len(hits)
        if hits:
            bits = len(hits) * w.c - ident_bits(len(s1), k)
            best = (bits, {"coding": "derive-rhs", "support": len(s1), "hits": len(hits), "exc": k})
    if len(t1) == 1 and rel_of(t1[0]) not in rels2:
        r2 = eval_term(w, t2)
        if r2:
            s1 = {p for p in eval_term(w, t1) if keep(p) and in_scope(w, t2, *p)}
            hits = s1 & r2
            k = len(s1) - len(hits)
            if hits:
                bits = len(hits) * (w.c - math.log2(len(r2))) - ident_bits(len(s1), k)
                if best is None or bits > best[0]:
                    best = (bits, {"coding": "index-lhs", "support": len(s1), "hits": len(hits), "exc": k})
    if best is None:
        return None
    return best[0] - law_bits(w, t1, t2) - COND_BITS, best[1]


def exc_share(info):
    return info["exc"] / info["support"] if info and info["support"] else 0.0


def exceptions_c(w, t1, t2, c=None):
    r2 = eval_term(w, t2)
    return sorted(p for p in domain(w, t1, t2, c) if p not in r2)

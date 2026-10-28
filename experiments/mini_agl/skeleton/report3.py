"""Readable report v3: holds(law, plane, status) with grounds, plane size, exceptions inside the plane and the
complement as a separate group. usage: report3.py WORLD SELECTION3 REPORT EXCEPTIONS"""
import sys

from candidates import split
from lawlib import World, eval_term, law_str, parse_law, read_world
from lawlib3 import domain, exceptions_c, keep_fn, parse_cond, saving_c

MONSTER_SHARE = 0.10


def sources(w, t1, t2, c):
    """Records supplying the facts behind derived (hit) pairs inside the plane."""
    cnt = {}
    keep = keep_fn(w, c)
    hits = {p for p in eval_term(w, t1) & eval_term(w, t2) if keep(p)}
    for x, y in sorted(hits):
        for t in (t1, t2):
            if len(t) == 1:
                at = t[0]
                p = (y, x) if at.endswith("~") else (x, y)
                for r in w.fact_recs.get((at.rstrip("~"), *p), ()):
                    cnt[r] = cnt.get(r, 0) + 1
            else:
                for z in sorted(w2 for (x2, w2) in eval_term(w, t[:1]) if x2 == x):
                    if (z, y) in eval_term(w, t[1:]):
                        for tt, pa in ((t[0], (x, z)), (t[1], (z, y))):
                            p = (pa[1], pa[0]) if tt.endswith("~") else pa
                            for r in w.fact_recs.get((tt.rstrip("~"), *p), ()):
                                cnt[r] = cnt.get(r, 0) + 1
    return cnt


def main():
    wpath, spath, rpath, epath = sys.argv[1:5]
    recs = read_world(wpath)
    find, hold = split(recs)
    wa, wf, wh = World(recs), World(find), World(hold)
    stats, rows, cols = {}, [], None
    for line in open(spath).read().splitlines():
        p = line.split("\t")
        if p[0] == "#stat":
            stats[p[1]] = int(p[2])
        elif p[0] == "#cols":
            cols = p[1:]
        elif not line.startswith("#"):
            rows.append(dict(zip(cols, p)))
    out = ["# report v3: records=%d find=%d hold=%d" % (len(recs), len(find), len(hold))]
    out += ["# %s=%d" % (k, stats[k]) for k in sorted(stats)]
    exc_lines = []
    planes_of = {r["law"] for r in rows if r["kind"] == "P" and r["selected"] == "1"}
    for r in rows:
        if r["kind"] == "U" and r["selected"] == "0":
            out.append("WITHDRAWN %s: exception share %s on finding observers (> 1/3); %s" % (
                r["law"], r["shareFind"], "plane found below" if r["law"] in planes_of else "no plane holds"))
    for r in rows:
        if r["selected"] != "1":
            continue
        t1, t2 = parse_law(r["law"])
        c = parse_cond(r["cond"])
        dom_all = domain(wa, t1, t2)
        dom = domain(wa, t1, t2, c)
        exc = exceptions_c(wa, t1, t2, c)
        comp = dom_all - dom
        r2 = eval_term(wa, t2)
        comp_exc = sorted(p for p in comp if p not in r2)
        share = len(dom) / len(dom_all) if dom_all else 0.0
        status = "exact" if not exc else "defeasible"
        sf, sh = saving_c(wf, t1, t2, c), saving_c(wh, t1, t2, c)
        out.append("HOLDS(%s, plane=%s, %s)" % (r["law"], "universal" if c is None else "{%s}" % r["cond"], status))
        out.append("  " + "  ".join("%s=%s" % kv for kv in zip(cols, [r[k] for k in cols])))
        out.append("  plane size: %d pairs of %d in the law's domain (%.0f%%)%s" % (
            len(dom), len(dom_all), 100 * share,
            "  FLAG monster-barring (< 10%%)" if c is not None and share < MONSTER_SHARE else ""))
        out.append("  find: %s  hold: %s" % (sf[1] if sf else None, sh[1] if sh else None))
        out.append("  grounds (records:facts): %s" % ", ".join("%s=%d" % kv for kv in sorted(sources(wa, t1, t2, c).items())))
        out.append("  exceptions inside plane (%d of %d): %s" % (
            len(exc), len(dom), " ".join("%s>%s" % e for e in exc[:8])))
        if c is not None:
            out.append("  complement (separate group): %d pairs, %d exceptions (%.0f%%)" % (
                len(comp), len(comp_exc), 100 * len(comp_exc) / len(comp) if comp else 0.0))
        exc_lines += ["%s\t%s\t%s\t%s" % (r["law"], r["cond"], x, y) for x, y in exc]
    with open(rpath, "w") as f:
        f.write("\n".join(out) + "\n")
    with open(epath, "w") as f:
        f.write("\n".join(exc_lines) + ("\n" if exc_lines else ""))


if __name__ == "__main__":
    main()

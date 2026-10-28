"""Readable report for selected laws. usage: report.py WORLD SELECTION REPORT EXCEPTIONS
Plane = where the law saves bits: finding half, held-out half, whole world, per-record roster slices."""
import sys

from candidates import split
from lawlib import World, eval_term, exceptions, law_str, parse_law, read_world, saving


def sources(w, t1, t2):
    """Records supplying the facts behind derived (hit) pairs."""
    cnt = {}
    hits = eval_term(w, t1) & eval_term(w, t2)
    for x, y in sorted(hits):
        for t, (a, b) in ((t1, (x, y)), (t2, (x, y))):
            if len(t) == 1:
                at = t[0]
                p = (b, a) if at.endswith("~") else (a, b)
                for r in w.fact_recs.get((at.rstrip("~"), *p), ()):
                    cnt[r] = cnt.get(r, 0) + 1
            else:
                first = t[:1]
                for z in sorted(w2 for (x2, w2) in eval_term(w, first) if x2 == x):
                    if (z, y) in eval_term(w, t[1:]):
                        for (tt, pa) in ((t[0], (x, z)), (t[1], (z, y))):
                            p = (pa[1], pa[0]) if tt.endswith("~") else pa
                            for r in w.fact_recs.get((tt.rstrip("~"), *p), ()):
                                cnt[r] = cnt.get(r, 0) + 1
    return cnt


def main():
    wpath, spath, rpath, epath = sys.argv[1:5]
    recs = read_world(wpath)
    find, hold = split(recs)
    wa, wf, wh = World(recs), World(find), World(hold)
    stats, sel = {}, []
    for line in open(spath).read().splitlines():
        p = line.split("\t")
        if p[0] == "#stat":
            stats[p[1]] = int(p[2])
        elif not line.startswith("#") and p[-1] == "1":
            sel.append((parse_law(p[0]), p))
    out = ["# report: records=%d find=%d hold=%d" % (len(recs), len(find), len(hold))]
    out += ["# %s=%d" % (k, stats[k]) for k in sorted(stats)]
    exc_lines = []
    for (t1, t2), p in sel:
        sa = saving(wa, t1, t2)
        exc = exceptions(wa, t1, t2)
        def holds(w):
            s = saving(w, t1, t2)
            return bool(s and s[0] > 0)

        planes = ["find:%s" % holds(wf), "hold:%s" % holds(wh), "all:%s" % holds(wa)]
        slices = []
        for rid in sorted(recs):
            ws = wa.restrict(recs[rid]["roster"])
            s = saving(ws, t1, t2)
            if s and s[0] > 0:
                slices.append(rid)
        out.append("LAW %s" % law_str(t1, t2))
        out.append("  c1 save(find)=%s  c2 twinMax=%s  c3 save(hold)=%s  c4 not derivable" % (p[1], p[2], p[4]))
        out.append("  all-world: %s" % (sa[1] if sa else None))
        out.append("  plane: %s; roster slices holding: %d/%d" % (", ".join(planes), len(slices), len(recs)))
        out.append("  sources: %s" % ", ".join("%s=%d" % kv for kv in sorted(sources(wa, t1, t2).items())))
        out.append("  exceptions (%d): %s" % (len(exc), " ".join("%s>%s" % e for e in exc[:8])))
        exc_lines += ["%s\t%s\t%s" % (law_str(t1, t2), x, y) for x, y in exc]
    with open(rpath, "w") as f:
        f.write("\n".join(out) + "\n")
    with open(epath, "w") as f:
        f.write("\n".join(exc_lines) + ("\n" if exc_lines else ""))


if __name__ == "__main__":
    main()

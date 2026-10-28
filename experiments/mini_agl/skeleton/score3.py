"""Compare selection3 with the oracle (the only place the oracle is read).
usage: score3.py ORACLE|- SELECTION3 OUT -> key=value lines.
Oracle rule inside the plane: support (pairs of the left term satisfying the condition on the HIDDEN
population) >= 10 and misses <= 1/2. Sex is read only here, for the calculator check."""
import sys

from lawlib import World, eval_term, parse_law, rel_of
from lawlib3 import HIGH, MIN_PLANE, keep_fn, parse_cond


def main():
    opath, spath, out = sys.argv[1:4]
    rows, cols = [], None
    for line in open(spath).read().splitlines():
        p = line.split("\t")
        if p[0] == "#cols":
            cols = p[1:]
        elif not line.startswith("#"):
            r = dict(zip(cols, p))
            if r["selected"] == "1":
                rows.append(r)
    res = ["selected=%d" % len(rows), "selected_universal=%d" % sum(r["kind"] == "U" for r in rows),
           "selected_planes=%d" % sum(r["kind"] == "P" for r in rows)]
    if opath != "-":
        recs = {r: {"rel": r, "roster": set(), "facts": set()} for r in ("father", "mother", "partner", "raised_by")}
        sex = {}
        for line in open(opath).read().splitlines():
            p = line.split("\t")
            if p[0] == "T":
                recs[p[1]]["facts"].add((p[2], p[3]))
            elif p[0] == "S":
                sex[p[1]] = p[2]
        w = World(recs)
        false_sel, true_sel, tight, boundary_ok, details = [], 0, 0, 0, []
        proxy = taut = onesex = 0
        shares, oshares = [], []
        for r in rows:
            t1, t2 = parse_law(r["law"])
            c = parse_cond(r["cond"])
            a, b = eval_term(w, t1), eval_term(w, t2)
            keep = keep_fn(w, c)
            ap = {p for p in a if keep(p)}
            miss_full = len(a - b)
            miss = len(ap - b)
            ok = len(ap) >= MIN_PLANE and miss * 2 <= len(ap)
            tt = len(ap) >= MIN_PLANE and miss <= HIGH * len(ap)
            bound = len(a) >= MIN_PLANE and miss_full > HIGH * len(a)
            true_sel += ok
            tight += tt
            if not ok:
                false_sel.append("%s|%s" % (r["law"], r["cond"]))
            flags = []
            if c is not None:
                boundary_ok += bound and tt
                shares.append(len(ap) / len(a) if a else 0.0)
                v = c[0]
                fin = [sex.get(p[v], "?") for p in ap]
                fout = [sex.get(p[v], "?") for p in a - ap]
                fi = fin.count("f") / len(fin) if fin else -1.0
                fo = fout.count("f") / len(fout) if fout else -1.0
                if fi >= 0 and (fi >= 0.9 or fi <= 0.1):
                    onesex += 1
                    flags.append("plane-one-sex")
                if fi >= 0 and fo >= 0 and ((fi >= 0.9 and fo <= 0.1) or (fi <= 0.1 and fo >= 0.9)):
                    proxy += 1
                    flags.append("sex-proxy")
                if c[2] in {rel_of(x) for x in t2}:
                    taut += 1
                    flags.append("cond-rel-in-rhs")
                details.append("%s|%s:hid_domain=%d,hid_plane=%d,miss_plane=%d,miss_full=%d,f_in=%.2f,f_out=%.2f,%s" % (
                    r["law"], r["cond"], len(a), len(ap), miss, miss_full, fi, fo, "+".join(flags) or "-"))
            else:
                oshares.append(miss_full / len(a) if a else 1.0)
                details.append("%s|-:hid_domain=%d,miss_full=%d" % (r["law"], len(a), miss_full))
        res += ["true_in_plane=%d" % true_sel, "false_in_plane=%d" % len(false_sel),
                "false_list=%s" % ";".join(false_sel), "tight_planes_le_third=%d" % tight,
                "boundary_laws_with_tight_plane=%d" % boundary_ok, "plane_one_sex=%d" % onesex,
                "sex_proxy_planes=%d" % proxy, "cond_rel_in_rhs=%d" % taut,
                "plane_share_hidden=%s" % ",".join("%.2f" % s for s in shares),
                "detail=%s" % " ;; ".join(details)]
    with open(out, "w") as f:
        f.write("\n".join(res) + "\n")


if __name__ == "__main__":
    main()

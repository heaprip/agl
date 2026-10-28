"""Compare selection with the oracle (the only place the oracle is read).
usage: score.py ORACLE|- SELECTION EXCEPTIONS OUT  -> key=value lines"""
import sys

from lawlib import World, canon_law, eval_term, law_str, parse_law


def main():
    opath, spath, epath, out = sys.argv[1:5]
    sel = [parse_law(l.split("\t")[0]) for l in open(spath).read().splitlines()
           if l and not l.startswith("#") and l.split("\t")[-1] == "1"]
    res = ["selected=%d" % len(sel)]
    if opath != "-":
        recs = {r: {"rel": r, "roster": set(), "facts": set()} for r in ("father", "mother", "partner", "raised_by")}
        designed = set()
        for line in open(opath).read().splitlines():
            p = line.split("\t")
            if p[0] == "T":
                recs[p[1]]["facts"].add((p[2], p[3]))
            elif p[0] == "D":
                designed.add(law_str(*canon_law(*parse_law(p[1]))))
        w = World(recs)
        true_exact, true_exc, false_sel = [], [], []
        truth = {}
        for t1, t2 in sel:
            a, b = eval_term(w, t1), eval_term(w, t2)
            miss = len(a - b)
            truth[law_str(t1, t2)] = (len(a), miss)
            if len(a) >= 10 and miss == 0:
                true_exact.append(law_str(t1, t2))
            elif len(a) >= 10 and miss * 2 <= len(a):
                true_exc.append(law_str(t1, t2))
            else:
                false_sel.append(law_str(t1, t2))
        listed = [l.split("\t") for l in open(epath).read().splitlines() if l]
        real = 0
        for law, x, y in listed:
            t1, t2 = parse_law(law)
            real += (x, y) not in eval_term(w, t2)
        res += ["true_exact=%d" % len(true_exact), "true_with_exceptions=%d" % len(true_exc),
                "false_selected=%d" % len(false_sel), "false_list=%s" % ";".join(false_sel),
                "designed_selected=%d" % len({law_str(*x) for x in sel} & designed),
                "designed_total=%d" % len(designed),
                "nondesigned_selected=%d" % len({law_str(*x) for x in sel} - designed),
                "exceptions_listed=%d" % len(listed), "exceptions_real_violations=%d" % real,
                "truth=%s" % ";".join("%s:%d/%d" % (k, v[1], v[0]) for k, v in sorted(truth.items()))]
    with open(out, "w") as f:
        f.write("\n".join(res) + "\n")


if __name__ == "__main__":
    main()

"""R2 evaluation (outside the mechanism). usage: predict_real.py WORLD SELECTION3 HIDDEN OUT
WORLD = the (reduced) world the selection was made on; HIDDEN = facts hidden from all records (rel, x, y).
For every selected (law, plane) whose right side is a single mother/father atom, predicts the pairs of the
left side (inside the plane) that no record gives; counts which of them are hidden facts (correct).
Transfer = left side is NOT a single atom of {mother, father, raised_by} (multi-atom or partner)."""
import sys

from lawlib import World, eval_term, parse_law, read_world, rel_of
from lawlib3 import keep_fn, parse_cond

MIRROR = {"mother", "father", "raised_by"}


def main():
    wpath, spath, hpath, out = sys.argv[1:5]
    w = World(read_world(wpath))
    hid = {tuple(l.split("\t")) for l in open(hpath).read().splitlines() if l}
    cols, sel = None, []
    for line in open(spath).read().splitlines():
        p = line.split("\t")
        if p[0] == "#cols":
            cols = p[1:]
        elif not line.startswith("#"):
            r = dict(zip(cols, p))
            if r["selected"] == "1":
                sel.append(r)
    lines, tot = [], {"pred": 0, "ok": 0, "tpred": 0, "tok": 0}
    for r in sel:
        t1, t2 = parse_law(r["law"])
        c = parse_cond(r["cond"]) if r["kind"] == "P" else None
        if len(t2) != 1 or rel_of(t2[0]) not in ("mother", "father"):
            lines.append("skip\t%s\t%s\tright side not a mother/father atom" % (r["law"], r["cond"]))
            continue
        rel, inv = rel_of(t2[0]), t2[0].endswith("~")
        keep = keep_fn(w, c)
        pred = set()
        for p in eval_term(w, t1):
            if not keep(p):
                continue
            f = (p[1], p[0]) if inv else p
            if f not in w.tuples.get(rel, ()):
                pred.add(f)
        ok = sum(1 for f in pred if (rel,) + f in hid)
        transfer = len(t1) > 1 or rel_of(t1[0]) not in MIRROR
        tot["pred"] += len(pred)
        tot["ok"] += ok
        if transfer:
            tot["tpred"] += len(pred)
            tot["tok"] += ok
        lines.append("law\t%s\t%s\t%s\tpredicted=%d\tcorrect=%d\t%s" % (
            r["law"], r["cond"], "transfer" if transfer else "mirror", len(pred), ok, rel))
    with open(out, "w") as f:
        f.write("hidden=%d\nselected=%d\npredicted=%d\ncorrect=%d\ntransfer_predicted=%d\ntransfer_correct=%d\n" % (
            len(hid), len(sel), tot["pred"], tot["ok"], tot["tpred"], tot["tok"]))
        f.write("\n".join(lines) + ("\n" if lines else ""))


if __name__ == "__main__":
    main()

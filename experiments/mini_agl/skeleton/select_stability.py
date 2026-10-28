"""Law selection v2.1 (plan skeleton-v2-plan.md, revision v2.1): stability selection with a sparse
base selector (top-q by saving among saving > 0, q from the bound), then Webb-style check on
held-out observers against degree-preserving twins, then ordering + redundancy pruning.
usage: select_stability.py WORLD CANDIDATES SEED OUT
Bound: Meinshausen & Buhlmann 2010, Theorem 1: E(V) <= q^2 / ((2*pi_thr - 1) * p); pi_thr = 0.9,
E(V) <= 1  =>  q = floor(sqrt(1 * p * 0.8))."""
import math
import random
import sys

import lawlib
from candidates import split
from lawlib import World, degree_switch, law_str, parse_law, read_world, saving
from select_laws import derivable

B = 100
TWINS = 1000
ALPHA = 0.05
E_V = 1.0           # target expected number of false selections
PI_THR = 0.9


def base_selected(w, laws, q):
    """Top-q laws by saving among those with saving > 0 (ties by name)."""
    pos = []
    for k, (t1, t2) in enumerate(laws):
        s = saving(w, t1, t2)
        if s and s[0] > 0:
            pos.append((-s[0], law_str(t1, t2), k))
    pos.sort()
    chosen = {k for _, _, k in pos[:q]}
    return [k in chosen for k in range(len(laws))]


def main():
    assert lawlib.EXC_CODE == "binom", "plan code of exceptions is binom"
    wpath, cpath, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    recs = read_world(wpath)
    find, hold = split(recs)
    wf, wh = World(find), World(hold)
    laws = [parse_law(l.split("\t")[0]) for l in open(cpath).read().splitlines() if l]
    p = len(laws)
    qcap = int(math.floor(math.sqrt(E_V * p * (2 * PI_THR - 1))))
    by_rel = {}
    for rid in sorted(find):
        by_rel.setdefault(find[rid]["rel"], []).append(rid)

    # --- stability: B subsamples, half of the finding observers per relation
    counts = [0] * p
    qsum = 0
    for j in range(B):
        rng = random.Random("sub:%d:%d" % (seed, j))
        pick = []
        for rel in sorted(by_rel):
            pick += rng.sample(by_rel[rel], len(by_rel[rel]) // 2)
        ws = World({rid: find[rid] for rid in sorted(pick)})
        sel = base_selected(ws, laws, qcap)
        for k, v in enumerate(sel):
            counts[k] += v
        qsum += sum(sel)
    pi = [c / B for c in counts]
    q = qsum / B
    bound = qcap * qcap / ((2 * PI_THR - 1) * p) if p else 0.0
    stable = [pi[k] >= PI_THR for k in range(p)]
    vacuous = False

    # --- held-out check against degree-preserving twins (shared by both modes)
    fs = [saving(wf, t1, t2) for t1, t2 in laws]
    c1 = [bool(s and s[0] > 0) for s in fs]
    ob = [saving(wh, t1, t2) for t1, t2 in laws]
    need = [k for k in range(p) if c1[k] or stable[k]]
    ge = {k: 0 for k in need}
    for j in range(TWINS):
        tw = World({rid: {"rel": r["rel"], "roster": set(r["roster"]),
                          "facts": degree_switch(r["facts"], random.Random("dt:%d:%d:%s" % (seed, j, rid)))}
                    for rid, r in sorted(hold.items())})
        tw.scope_cache = wh.scope_cache  # same rosters as the held-out world
        for k in need:
            o = ob[k]
            if o is None or o[0] <= 0:
                continue
            s = saving(tw, *laws[k])
            if s is not None and s[0] >= o[0]:
                ge[k] += 1
    pv = {}
    for k in need:
        o = ob[k]
        pv[k] = 1.0 if (o is None or o[0] <= 0) else (1 + ge[k]) / (1 + TWINS)
    n_c1 = sum(c1)
    alone = [k in pv and c1[k] and pv[k] <= ALPHA / max(1, n_c1) for k in range(p)]
    write(out, laws, p, pi, q, qcap, bound, stable, fs, c1, pv, alone, n_c1)


def write(out, laws, p, pi, q, qcap, bound, stable, fs, c1, pv, alone, n_c1):
    m = sum(stable)
    webb = [k in pv and stable[k] and pv[k] <= ALPHA / max(1, m) for k in range(p)]
    passed = sorted((k for k in range(p) if webb[k]), key=lambda k: (-fs[k][0], law_str(*laws[k])))
    selected = []
    blocked = 0
    for k in passed:
        if derivable(selected, *laws[k]):
            blocked += 1
        else:
            selected.append(laws[k])
    sel_set = set(selected)
    stats = {"candidates": p, "c1": n_c1, "stable": m, "webb_pass": sum(webb), "derivable_blocked": blocked,
             "selected": len(selected),
             "stability_decisive": sum(1 for k in range(p) if c1[k] and not stable[k] and alone[k]),
             "webb_decisive": sum(1 for k in range(p) if stable[k] and not webb[k]),
             "qcap": qcap}
    with open(out, "w") as f:
        for k in sorted(stats):
            f.write("#stat\t%s\t%d\n" % (k, stats[k]))
        f.write("#info\tqcap=%d\tq_mean=%.3f\tbound_EV=%.3f\tpi_thr=%.2f\n" % (qcap, q, bound, PI_THR))
        f.write("#cols\tlaw\tsaveFind\tpi\tstable\tp_webb\twebb\tselected\n")
        for k in sorted(range(p), key=lambda k: (-(fs[k][0] if fs[k] else -1e9), law_str(*laws[k]))):
            if not (c1[k] or pi[k] > 0):
                continue
            f.write("%s\t%s\t%.2f\t%d\t%s\t%d\t%d\n" % (
                law_str(*laws[k]), "-" if fs[k] is None else "%.1f" % fs[k][0], pi[k], stable[k],
                "-" if k not in pv else "%.4f" % pv[k], webb[k], laws[k] in sel_set))


if __name__ == "__main__":
    main()

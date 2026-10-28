"""Law with plane (plan skeleton-v3-plan.md, H115). usage: select_plane.py WORLD CANDIDATES SEL21 SEED OUT
SEL21 = selection of v2.1 (select_stability.py). Steps: universal v2.1 laws with a high exception share
(> 1/3 on finding observers) are withdrawn; for every candidate with a high share a one-atom condition
is searched (pool); the pool goes through the same stability selection (top-q, q from the bound,
pi_thr = 0.9, B = 100) and the same held-out Webb check (degree-preserving twins, Bonferroni by stable)."""
import math
import random
import sys

import lawlib
from candidates import split
from lawlib import World, degree_switch, law_str, parse_law, read_world, saving
from lawlib3 import CONDS, HIGH, MIN_PLANE, cond_name, domain, exc_share, saving_c
from select_stability import ALPHA, B, E_V, PI_THR, TWINS


def build_pool(wf, laws):
    """Returns (flagged laws, pool entries (t1, t2, cond))."""
    flagged, pool = [], []
    for t1, t2 in laws:
        s = saving(wf, t1, t2)
        if s is None or exc_share(s[1]) <= HIGH:
            continue
        flagged.append((t1, t2))
        full = domain(wf, t1, t2)
        seen = set()
        for c in CONDS:
            dom = frozenset(domain(wf, t1, t2, c))
            if len(dom) < MIN_PLANE or len(dom) >= len(full) or dom in seen:
                continue
            sc = saving_c(wf, t1, t2, c)
            if sc is None or exc_share(sc[1]) > HIGH:
                continue
            seen.add(dom)
            pool.append((t1, t2, c))
    pool.sort(key=lambda e: (law_str(e[0], e[1]), cond_name(e[2])))
    return flagged, pool


def base_selected_c(w, pool, q):
    pos = []
    for k, (t1, t2, c) in enumerate(pool):
        s = saving_c(w, t1, t2, c)
        if s and s[0] > 0:
            pos.append((-s[0], law_str(t1, t2), cond_name(c), k))
    pos.sort()
    chosen = {e[3] for e in pos[:q]}
    return [k in chosen for k in range(len(pool))]


def main():
    assert lawlib.EXC_CODE == "binom", "plan code of exceptions is binom"
    wpath, cpath, spath, seed, out = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
    recs = read_world(wpath)
    find, hold = split(recs)
    wf, wh = World(find), World(hold)
    laws = [parse_law(l.split("\t")[0]) for l in open(cpath).read().splitlines() if l]
    sel21 = [parse_law(l.split("\t")[0]) for l in open(spath).read().splitlines()
             if l and not l.startswith("#") and l.split("\t")[-1] == "1"]
    flagged, pool = build_pool(wf, laws)
    p = len(pool)
    qcap = int(math.floor(math.sqrt(E_V * p * (2 * PI_THR - 1))))
    by_rel = {}
    for rid in sorted(find):
        by_rel.setdefault(find[rid]["rel"], []).append(rid)

    counts = [0] * p
    qsum = 0
    if p:
        for j in range(B):
            rng = random.Random("subp:%d:%d" % (seed, j))
            pick = []
            for rel in sorted(by_rel):
                pick += rng.sample(by_rel[rel], len(by_rel[rel]) // 2)
            ws = World({rid: find[rid] for rid in sorted(pick)})
            sel = base_selected_c(ws, pool, qcap)
            for k, v in enumerate(sel):
                counts[k] += v
            qsum += sum(sel)
    pi = [c / B for c in counts]
    stable = [pi[k] >= PI_THR for k in range(p)]
    fs = [saving_c(wf, *e) for e in pool]
    c1 = [bool(s and s[0] > 0) for s in fs]
    ob = [saving_c(wh, *e) for e in pool]
    need = [k for k in range(p) if c1[k] or stable[k]]
    ge = {k: 0 for k in need}
    if need:
        for j in range(TWINS):
            tw = World({rid: {"rel": r["rel"], "roster": set(r["roster"]),
                              "facts": degree_switch(r["facts"], random.Random("dt:%d:%d:%s" % (seed, j, rid)))}
                        for rid, r in sorted(hold.items())})
            tw.scope_cache = wh.scope_cache
            for k in need:
                o = ob[k]
                if o is None or o[0] <= 0:
                    continue
                s = saving_c(tw, *pool[k])
                if s is not None and s[0] >= o[0]:
                    ge[k] += 1
    pv = {k: (1.0 if (ob[k] is None or ob[k][0] <= 0) else (1 + ge[k]) / (1 + TWINS)) for k in need}
    n_c1 = sum(c1)
    m = sum(stable)
    alone = [k in pv and c1[k] and pv[k] <= ALPHA / max(1, n_c1) for k in range(p)]
    webb = [k in pv and stable[k] and pv[k] <= ALPHA / max(1, m) for k in range(p)]

    # universal part: withdrawn when the share on finding observers is high
    univ = []
    for t1, t2 in sel21:
        s = saving(wf, t1, t2)
        sh = exc_share(s[1]) if s else 0.0
        univ.append((t1, t2, s, sh, sh <= HIGH))
    planes_by_law = {}
    for k in range(p):
        if webb[k]:
            planes_by_law.setdefault(law_str(pool[k][0], pool[k][1]), []).append(k)
    stats = {"candidates": len(laws), "high_share_laws": len(flagged), "v21_selected": len(sel21),
             "universal_kept": sum(1 for u in univ if u[4]), "universal_withdrawn": sum(1 for u in univ if not u[4]),
             "pool": p, "qcap": qcap, "c1": n_c1, "stable": m, "webb_pass": sum(webb),
             "selected_planes": sum(webb), "laws_with_plane": len(planes_by_law),
             "high_laws_without_plane": sum(1 for t1, t2 in flagged if law_str(t1, t2) not in planes_by_law),
             "stability_decisive": sum(1 for k in range(p) if c1[k] and not stable[k] and alone[k]),
             "webb_decisive": sum(1 for k in range(p) if stable[k] and not webb[k])}
    bound = qcap * qcap / ((2 * PI_THR - 1) * p) if p else 0.0
    with open(out, "w") as f:
        for k in sorted(stats):
            f.write("#stat\t%s\t%d\n" % (k, stats[k]))
        f.write("#info\tqcap=%d\tq_mean=%.3f\tbound_EV=%.3f\tpi_thr=%.2f\n" % (qcap, qsum / B, bound, PI_THR))
        f.write("#cols\tkind\tlaw\tcond\tsaveFind\tshareFind\tsupFind\tpi\tstable\tp_webb\twebb\tshareHold\tselected\n")
        for t1, t2, s, sh, ok in sorted(univ, key=lambda u: law_str(u[0], u[1])):
            f.write("U\t%s\t-\t%s\t%.3f\t%d\t-\t-\t-\t-\t-\t%d\n" % (
                law_str(t1, t2), "%.1f" % s[0] if s else "-", sh, s[1]["support"] if s else 0, ok))
        for k in sorted(range(p), key=lambda k: (-(fs[k][0] if fs[k] else -1e9), law_str(*pool[k][:2]),
                                                  cond_name(pool[k][2]))):
            if not (c1[k] or pi[k] > 0):
                continue
            t1, t2, c = pool[k]
            f.write("P\t%s\t%s\t%s\t%.3f\t%d\t%.2f\t%d\t%s\t%d\t%s\t%d\n" % (
                law_str(t1, t2), cond_name(c), "%.1f" % fs[k][0] if fs[k] else "-", exc_share(fs[k][1]) if fs[k] else 0.0,
                fs[k][1]["support"] if fs[k] else 0, pi[k], stable[k], "-" if k not in pv else "%.4f" % pv[k],
                webb[k], "-" if not ob[k] else "%.3f" % exc_share(ob[k][1]), webb[k]))


if __name__ == "__main__":
    main()

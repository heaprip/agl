"""Law selection by the four H113 conditions. usage: select_laws.py WORLD CANDIDATES SEED OUT
Only candidates with saving > 0 on the finding half (condition 1) are examined further."""
import random
import sys

from candidates import split
from lawlib import (World, inv_term, law_str, parse_law, read_world, saving)

TWINS = 20
MAX_LEN = 3


def twin_world(find, seed, j):
    rec = {}
    for rid in sorted(find):
        r = find[rid]
        rng = random.Random("twin:%d:%d:%s" % (seed, j, rid))
        roster = sorted(r["roster"])
        facts = set()
        while len(facts) < min(len(r["facts"]), len(roster) * (len(roster) - 1)):
            x, y = rng.choice(roster), rng.choice(roster)
            if x != y:
                facts.add((x, y))
        rec[rid] = {"rel": r["rel"], "roster": set(r["roster"]), "facts": facts}
    return World(rec)


def derivable(selected, t1, t2):
    """Condition 4: can t2 be reached from t1 by rewriting with selected laws (and their
    inverses; subterm replacement gives monotonicity, chaining gives transitivity)?"""
    rules = []
    for a, b in selected:
        rules += [(a, b), (inv_term(a), inv_term(b))]
    seen, todo = {t1}, [t1]
    while todo:
        t = todo.pop()
        if t == t2:
            return True
        for x, y in rules:
            for i in range(len(t) - len(x) + 1):
                if t[i:i + len(x)] == x:
                    n = t[:i] + y + t[i + len(x):]
                    if len(n) <= MAX_LEN and n not in seen:
                        seen.add(n)
                        todo.append(n)
    return False


def main():
    wpath, cpath, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    recs = read_world(wpath)
    find, hold = split(recs)
    wf, wh = World(find), World(hold)
    laws = [parse_law(l.split("\t")[0]) for l in open(cpath).read().splitlines() if l]
    twins = [twin_world(find, seed, j) for j in range(TWINS)]
    rows, stats = [], {"candidates": len(laws), "c1": 0, "c1c2": 0, "c1c3": 0, "c1c2c3": 0,
                       "only_twin_blocks": 0, "only_holdout_blocks": 0, "selected": 0,
                       "derivable_blocked": 0}
    passed = []
    for t1, t2 in laws:
        s = saving(wf, t1, t2)
        if s is None or s[0] <= 0:
            continue
        stats["c1"] += 1
        tw = [saving(w, t1, t2) for w in twins]
        tmax = max([x[0] for x in tw if x] or [0.0])
        c2 = tmax <= 0
        sh = saving(wh, t1, t2)
        c3 = sh is not None and sh[0] > 0
        stats["c1c2"] += c2
        stats["c1c3"] += c3
        stats["c1c2c3"] += c2 and c3
        stats["only_twin_blocks"] += (not c2) and c3
        stats["only_holdout_blocks"] += c2 and not c3
        rows.append([t1, t2, s[0], tmax, c2, sh[0] if sh else None, c3])
        if c2 and c3:
            passed.append((t1, t2, s[0]))
    passed.sort(key=lambda p: (-p[2], law_str(p[0], p[1])))
    selected, sel_keys = [], set()
    for t1, t2, bits in passed:
        if derivable(selected, t1, t2):
            stats["derivable_blocked"] += 1
            continue
        selected.append((t1, t2))
        sel_keys.add((t1, t2))
    stats["selected"] = len(selected)
    rows.sort(key=lambda r: (-r[2], law_str(r[0], r[1])))
    with open(out, "w") as f:
        for k in sorted(stats):
            f.write("#stat\t%s\t%d\n" % (k, stats[k]))
        f.write("#cols\tlaw\tsaveFind\ttwinMax\tc2\tsaveHold\tc3\tselected\n")
        for t1, t2, s1, tm, c2, sh, c3 in rows:
            f.write("%s\t%.1f\t%.1f\t%d\t%s\t%d\t%d\n" % (
                law_str(t1, t2), s1, tm, c2, "-" if sh is None else "%.1f" % sh, c3,
                (t1, t2) in sel_keys))


if __name__ == "__main__":
    main()

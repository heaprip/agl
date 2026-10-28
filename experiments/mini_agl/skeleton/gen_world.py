"""World generator. usage: gen_world.py KIND SEED OUTDIR [SRCDIR]
KIND: A (hidden kinship population + observers), twin / broken (from SRCDIR/world.tsv), random.
Writes OUTDIR/world.tsv (+ OUTDIR/oracle.tsv for A). The pipeline never reads the oracle."""
import os
import random
import sys

from lawlib import read_world, write_world

REL_ORDER = ["father", "mother", "partner", "raised_by"]
OBSERVERS = 4
ROSTER_P = 0.85
KEEP_P = 0.9


def population(rng):
    """Hidden truth: returns (facts per relation, sexes, ids)."""
    nid = [0]
    sex = {}
    facts = {r: set() for r in REL_ORDER}

    def new(s):
        nid[0] += 1
        sex[nid[0]] = s
        return nid[0]

    couples = []
    for _ in range(14):
        couples.append((new("f"), new("m")))
    pairs_now = {}  # current partner map
    for g in range(5):
        kids_all = []
        for mo, fa in couples:
            kids = []
            if rng.random() < 0.85:
                kids = [new(rng.choice("fm")) for _ in range(rng.choice([1, 2, 2, 3, 4]))]
            for c in kids:
                facts["mother"].add((mo, c))
                facts["father"].add((fa, c))
            sep = bool(kids) and rng.random() < 0.3
            if not sep:
                pairs_now[mo], pairs_now[fa] = fa, mo
                for c in kids:
                    facts["raised_by"] |= {(c, mo), (c, fa)}
            else:
                cust = mo if rng.random() < 0.6 else fa
                for p in (mo, fa):
                    if rng.random() < 0.6:
                        o = new("m" if sex[p] == "f" else "f")
                        pairs_now[p], pairs_now[o] = o, p
                for c in kids:
                    facts["raised_by"].add((c, cust))
                    if cust in pairs_now:
                        facts["raised_by"].add((c, pairs_now[cust]))
            kids_all.append(kids)
        # next generation couples: opposite sex, different sibling groups
        girls = [c for k in kids_all for c in k if sex[c] == "f"]
        boys = [c for k in kids_all for c in k if sex[c] == "m"]
        grp = {c: i for i, k in enumerate(kids_all) for c in k}
        rng.shuffle(girls)
        rng.shuffle(boys)
        couples = []
        for gi in girls:
            for bj in boys:
                if grp[gi] != grp[bj]:
                    boys.remove(bj)
                    couples.append((gi, bj))
                    break
    for p, q in sorted(pairs_now.items()):
        facts["partner"].add((p, q))
    # last generation couples not yet in pairs_now
    for mo, fa in couples:
        facts["partner"] |= {(mo, fa), (fa, mo)}
    return facts, sex, nid[0]


def observe(rng, facts, ids):
    """Several independent incomplete records per relation, overlapping by person ids."""
    recs = {}
    names = lambda i: "p%04d" % i  # noqa: E731
    perm = list(range(1, ids + 1))
    rng.shuffle(perm)
    lab = {i: names(perm[i - 1]) for i in range(1, ids + 1)}  # opaque labels
    for rel in REL_ORDER:
        for k in range(OBSERVERS):
            roster = {lab[i] for i in range(1, ids + 1) if rng.random() < ROSTER_P}
            fs = set()
            for x, y in sorted(facts[rel]):
                a, b = lab[x], lab[y]
                if a in roster and b in roster and rng.random() < KEEP_P:
                    fs.add((a, b))
                    if rel == "partner":  # symmetric relation is written both ways
                        fs.add((b, a))
            recs["%s%d" % (rel[:3], k)] = {"rel": rel, "roster": roster, "facts": fs}
    return recs, lab


def random_fill(rng, roster, count):
    r = sorted(roster)
    out = set()
    while len(out) < min(count, len(r) * (len(r) - 1)):
        x, y = rng.choice(r), rng.choice(r)
        if x != y:
            out.add((x, y))
    return out


def main():
    kind, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    os.makedirs(out, exist_ok=True)
    rng = random.Random("world:%s:%d" % (kind, seed))
    if kind == "A":
        facts, sex, ids = population(random.Random("pop:%d" % seed))
        recs, lab = observe(random.Random("obs:%d" % seed), facts, ids)
        with open(os.path.join(out, "oracle.tsv"), "w") as f:
            for rel in REL_ORDER:
                for x, y in sorted((lab[a], lab[b]) for a, b in facts[rel]):
                    f.write("T\t%s\t%s\t%s\n" % (rel, x, y))
            for i in range(1, ids + 1):
                f.write("S\t%s\t%s\n" % (lab[i], sex[i]))
            for d in ["mother~ <= raised_by", "father~ <= raised_by",
                      "father~;partner <= raised_by", "mother~;partner <= raised_by"]:
                f.write("D\t%s\n" % d)
    elif kind == "twin":
        src = read_world(os.path.join(sys.argv[4], "world.tsv"))
        recs = {rid: {"rel": r["rel"], "roster": set(r["roster"]),
                      "facts": random_fill(rng, r["roster"], len(r["facts"]))}
                for rid, r in sorted(src.items())}
    elif kind == "broken":
        src = read_world(os.path.join(sys.argv[4], "world.tsv"))
        recs = {rid: {"rel": r["rel"], "roster": {"%s:%s" % (rid, p) for p in r["roster"]},
                      "facts": {("%s:%s" % (rid, x), "%s:%s" % (rid, y)) for x, y in r["facts"]}}
                for rid, r in sorted(src.items())}
    elif kind == "random":
        people = ["q%04d" % i for i in range(170)]
        counts = {"father": 45, "mother": 45, "partner": 80, "raised_by": 80}
        recs = {}
        for rel in REL_ORDER:
            for k in range(OBSERVERS):
                roster = {p for p in people if rng.random() < ROSTER_P}
                recs["%s%d" % (rel[:3], k)] = {"rel": rel, "roster": roster,
                                               "facts": random_fill(rng, roster, counts[rel])}
    else:
        raise SystemExit("unknown kind")
    write_world(os.path.join(out, "world.tsv"), recs)
    # same world with shuffled row order, for the permutation check
    write_world(os.path.join(out, "world_shuffled.tsv"), recs, random.Random("shuffle:%d" % seed))


if __name__ == "__main__":
    main()

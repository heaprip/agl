"""World generator v2 (skeleton v2 plan). usage: gen_world2.py KIND SEED OUTDIR [SRCDIR]
KIND: A2 (hidden population as in v1, 8 observers per relation with own coverage, loss, noise),
twin / broken / degtwin (from SRCDIR/world.tsv), random. Writes OUTDIR/world.tsv, world_shuffled.tsv
(+ oracle.tsv for A2). The pipeline never reads the oracle."""
import os
import random
import sys

from gen_world import REL_ORDER, population, random_fill
from lawlib import degree_switch, read_world, write_world

OBSERVERS = 8
COVER = (0.45, 0.80)
LOSS = (0.05, 0.30)
NOISE = (0.0, 0.05)


def observe2(rng, facts, ids):
    perm = list(range(1, ids + 1))
    rng.shuffle(perm)
    lab = {i: "p%04d" % perm[i - 1] for i in range(1, ids + 1)}
    recs = {}
    for rel in REL_ORDER:
        for k in range(OBSERVERS):
            cover = rng.uniform(*COVER)
            loss = rng.uniform(*LOSS)
            noise = rng.uniform(*NOISE)
            roster = {lab[i] for i in range(1, ids + 1) if rng.random() < cover}
            fs = set()
            for x, y in sorted(facts[rel]):
                a, b = lab[x], lab[y]
                if a in roster and b in roster and rng.random() >= loss:
                    fs.add((a, b))
                    if rel == "partner":
                        fs.add((b, a))
            rl = sorted(roster)
            for _ in range(int(round(noise * len(fs)))):  # false facts: wrong target from the roster
                x, y = rng.choice(rl), rng.choice(rl)
                if x != y:
                    fs.add((x, y))
            recs["%s%d" % (rel[:3], k)] = {"rel": rel, "roster": roster, "facts": fs}
    return recs, lab


def main():
    kind, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    os.makedirs(out, exist_ok=True)
    rng = random.Random("world2:%s:%d" % (kind, seed))
    if kind == "A2":
        facts, sex, ids = population(random.Random("pop:%d" % seed))
        recs, lab = observe2(random.Random("obs2:%d" % seed), facts, ids)
        with open(os.path.join(out, "oracle.tsv"), "w") as f:
            for rel in REL_ORDER:
                for x, y in sorted((lab[a], lab[b]) for a, b in facts[rel]):
                    f.write("T\t%s\t%s\t%s\n" % (rel, x, y))
            for i in range(1, ids + 1):
                f.write("S\t%s\t%s\n" % (lab[i], sex[i]))
            for d in ["mother~ <= raised_by", "father~ <= raised_by",
                      "father~;partner <= raised_by", "mother~;partner <= raised_by"]:
                f.write("D\t%s\n" % d)
    elif kind in ("twin", "broken", "degtwin"):
        src = read_world(os.path.join(sys.argv[4], "world.tsv"))
        if kind == "twin":
            recs = {rid: {"rel": r["rel"], "roster": set(r["roster"]),
                          "facts": random_fill(rng, r["roster"], len(r["facts"]))}
                    for rid, r in sorted(src.items())}
        elif kind == "degtwin":
            recs = {rid: {"rel": r["rel"], "roster": set(r["roster"]),
                          "facts": degree_switch(r["facts"], random.Random("deg:%d:%s" % (seed, rid)))}
                    for rid, r in sorted(src.items())}
        else:
            recs = {rid: {"rel": r["rel"], "roster": {"%s:%s" % (rid, p) for p in r["roster"]},
                          "facts": {("%s:%s" % (rid, x), "%s:%s" % (rid, y)) for x, y in r["facts"]}}
                    for rid, r in sorted(src.items())}
    elif kind == "random":
        people = ["q%04d" % i for i in range(170)]
        counts = {"father": 20, "mother": 20, "partner": 40, "raised_by": 40}
        recs = {}
        for rel in REL_ORDER:
            for k in range(OBSERVERS):
                cover = rng.uniform(*COVER)
                roster = {p for p in people if rng.random() < cover}
                recs["%s%d" % (rel[:3], k)] = {"rel": rel, "roster": roster,
                                               "facts": random_fill(rng, roster, counts[rel])}
    else:
        raise SystemExit("unknown kind")
    write_world(os.path.join(out, "world.tsv"), recs)
    write_world(os.path.join(out, "world_shuffled.tsv"), recs, random.Random("shuffle:%d" % seed))


if __name__ == "__main__":
    main()

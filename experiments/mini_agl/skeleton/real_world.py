"""Input adapter for the real-data experiment (plan: local/experiments/mini-agl/skeleton-real-plan.md).
The mechanism (v3) is not touched: this file only turns the Wikidata snapshot into the v3 world format.

usage:
  real_world.py snapshot SNAP.tsv SOURCES.tsv OUTDIR [hold]   snapshot -> OUTDIR/world.tsv (+ world_shuffled.tsv,
        sources.txt = label/name/counts; 'hold' also hides 1/5 of mother and father facts from ALL records
        -> OUTDIR/hidden.tsv)
  real_world.py randreal SRCDIR OUTDIR SEED                    size-matched random control from SRCDIR/world.tsv
Slot note: the 4th relation of v3 is called raised_by in lawlib3.RELS; here it holds P40 'child' as
(child, parent). Opaque labels: people pNNNN (seeded permutation), sources sNNN / s000 unreferenced / s999 minor."""
import hashlib
import os
import random
import sys

from gen_world import random_fill
from lawlib import read_world, write_world

MINOR = 5
HIDE_MOD = 5
SLOT = {"P25": "mother", "P22": "father", "P26": "partner", "P40": "raised_by"}


def read_snapshot(path):
    srcs = {}
    for line in open(path).read().splitlines():
        prop, s, o, src = line.split("\t")
        if prop in SLOT:
            srcs.setdefault((prop, s, o), set()).add(src)
    for k, v in srcs.items():  # '-' only when no P248 at all
        if len(v) > 1:
            v.discard("-")
    return srcs


def hidden(rel, x, y):
    h = hashlib.sha256(("hide:1:%s:%s:%s" % (rel, x, y)).encode()).hexdigest()
    return int(h, 16) % HIDE_MOD == 0


def build(snap, names, hold):
    people = sorted({q for (_, s, o) in snap for q in (s, o)}, key=lambda q: int(q[1:]))
    perm = list(range(1, len(people) + 1))
    random.Random("real-labels").shuffle(perm)
    lab = {q: "p%04d" % perm[i] for i, q in enumerate(people)}
    allsrc = sorted({s for v in snap.values() for s in v if s != "-"}, key=lambda q: int(q[1:]))
    slab = {q: "s%03d" % (i + 1) for i, q in enumerate(allsrc)}
    slab["-"] = "s000"
    per = {}  # (rel, srcQ) -> set of (x, y) in statement orientation
    hid = []
    for (prop, s, o), ss in sorted(snap.items()):
        rel = SLOT[prop]
        x, y = (o, s) if prop in ("P25", "P22", "P40") else (s, o)
        if prop == "P40":
            x, y = o, s  # (child, parent)
        if x == y:
            continue
        a, b = lab[x], lab[y]
        if hold and rel in ("mother", "father"):
            if hidden(rel, a, b):
                hid.append((rel, a, b))
                continue
        for src in ss:
            per.setdefault((rel, src), set()).add((a, b))
    recs, desc = {}, []
    minor = {}
    for (rel, src), fs in sorted(per.items()):
        if len(fs) < MINOR:
            minor.setdefault(rel, set()).update(fs)
            desc.append((rel, "s999", src, len(fs)))
            continue
        recs["%s_%s" % (rel[:3], slab[src])] = {"rel": rel, "facts": set(fs)}
        desc.append((rel, slab[src], src, len(fs)))
    for rel, fs in sorted(minor.items()):
        recs["%s_s999" % rel[:3]] = {"rel": rel, "facts": set(fs)}
    for r in recs.values():
        if r["rel"] == "partner":
            r["facts"] |= {(y, x) for x, y in r["facts"]}
        r["roster"] = {p for f in r["facts"] for p in f}
    return recs, desc, hid, slab, names


def main():
    mode = sys.argv[1]
    if mode == "snapshot":
        snap = read_snapshot(sys.argv[2])
        names = dict(l.split("\t", 1) for l in open(sys.argv[3]).read().splitlines() if l)
        out = sys.argv[4]
        hold = len(sys.argv) > 5 and sys.argv[5] == "hold"
        os.makedirs(out, exist_ok=True)
        recs, desc, hid, slab, names = build(snap, names, hold)
        write_world(os.path.join(out, "world.tsv"), recs)
        write_world(os.path.join(out, "world_shuffled.tsv"), recs, random.Random("shuffle:real"))
        inv = {v: k for k, v in slab.items()}
        with open(os.path.join(out, "sources.txt"), "w") as f:
            for rel, sl, src, n in sorted(desc, key=lambda d: (d[0], -d[3], d[1])):
                f.write("%s\t%s\t%s\t%s\t%d\n" % (rel, sl, src, names.get(src, "").strip() or "-", n))
            for rid in sorted(recs):
                f.write("#rec\t%s\t%s\tfacts=%d\troster=%d\n" % (rid, recs[rid]["rel"], len(recs[rid]["facts"]),
                                                              len(recs[rid]["roster"])))
        if hold:
            with open(os.path.join(out, "hidden.tsv"), "w") as f:
                for rel, a, b in sorted(hid):
                    f.write("%s\t%s\t%s\n" % (rel, a, b))
    elif mode == "randreal":
        src = read_world(os.path.join(sys.argv[2], "world.tsv"))
        out, seed = sys.argv[3], int(sys.argv[4])
        rng = random.Random("randreal:%d" % seed)
        os.makedirs(out, exist_ok=True)
        recs = {rid: {"rel": r["rel"], "roster": set(r["roster"]),
                      "facts": random_fill(rng, r["roster"], len(r["facts"]))} for rid, r in sorted(src.items())}
        write_world(os.path.join(out, "world.tsv"), recs)
        write_world(os.path.join(out, "world_shuffled.tsv"), recs, random.Random("shuffle:randreal:%d" % seed))
    else:
        raise SystemExit("unknown mode")


if __name__ == "__main__":
    main()

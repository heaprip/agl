"""Entry for the real-data experiment (plan: local/experiments/mini-agl/skeleton-real-plan.md).
usage: python3 run_real.py [OUTDIR] [SEEDS comma list] ; env SNAP / SRCS (default data/wikidata/...).
Worlds: real (full snapshot), hold (1/5 of mother/father hidden from all records), controls of real
(twin, broken, degtwin, random, randreal), holddeg (degree-preserving twin of hold). Mechanism = v3 stages,
unchanged (candidates, select_stability, select_plane, reports). R3 runs (rerun with another PYTHONHASHSEED,
shuffled rows) on seed 1 only. Summary: OUTDIR/summary.txt. EXC_CODE=binom forced."""
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out_real")
SEEDS = [int(s) for s in (sys.argv[2] if len(sys.argv) > 2 else "1,2,3").split(",")]
SNAP = os.environ.get("SNAP", os.path.join(ROOT, "data", "wikidata", "kinship-victoria.tsv"))
SRCS = os.environ.get("SRCS", os.path.join(ROOT, "data", "wikidata", "kinship-victoria-sources.tsv"))
F21 = ("candidates.tsv", "selection.tsv", "report.txt", "exceptions.tsv")
F3 = ("selection3.tsv", "report3.txt", "exceptions3.tsv")
CONTROLS = ["twin", "broken", "degtwin", "random", "randreal"]


def py(script, *args, hashseed="0"):
    env = dict(os.environ, PYTHONHASHSEED=hashseed, EXC_CODE="binom")
    subprocess.run([sys.executable, "-B", os.path.join(HERE, script), *map(str, args)], check=True,
                   env=env, cwd=HERE, stdout=subprocess.DEVNULL)


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]


def stats(path):
    st = {}
    for l in open(path):
        p = l.rstrip("\n").split("\t")
        if p[0] == "#stat":
            st[p[1]] = int(p[2])
    return st


def kv(path):
    return dict(l.split("=", 1) for l in open(path).read().splitlines() if "=" in l and "\t" not in l)


def pipeline(world, outdir, seed, hashseed):
    os.makedirs(outdir, exist_ok=True)
    cand, sel21, sel3 = (os.path.join(outdir, n) for n in ("candidates.tsv", "selection.tsv", "selection3.tsv"))
    py("candidates.py", world, cand, hashseed=hashseed)
    py("select_stability.py", world, cand, seed, sel21, hashseed=hashseed)
    py("report.py", world, sel21, os.path.join(outdir, "report.txt"), os.path.join(outdir, "exceptions.tsv"),
       hashseed=hashseed)
    py("select_plane.py", world, cand, sel21, seed, sel3, hashseed=hashseed)
    py("report3.py", world, sel3, os.path.join(outdir, "report3.txt"), os.path.join(outdir, "exceptions3.tsv"),
       hashseed=hashseed)
    return outdir


def same(a, b):
    return all(sha(os.path.join(a, f)) == sha(os.path.join(b, f)) for f in F21 + F3)


def main():
    os.makedirs(OUT, exist_ok=True)
    real, hold = os.path.join(OUT, "real"), os.path.join(OUT, "hold")
    py("real_world.py", "snapshot", SNAP, SRCS, real)
    py("real_world.py", "snapshot", SNAP, SRCS, hold, "hold")
    rows = []
    for seed in SEEDS:
        base = os.path.join(OUT, "seed%d" % seed)
        worlds = {"real": real, "hold": hold}
        for kind in CONTROLS:
            d = os.path.join(base, kind)
            if kind == "randreal":
                py("real_world.py", "randreal", real, d, seed)
            elif kind == "random":
                py("gen_world2.py", "random", seed, d)
            else:
                py("gen_world2.py", kind, seed, d, real)
            worlds[kind] = d
        d = os.path.join(base, "holddeg")
        py("gen_world2.py", "degtwin", seed, d, hold)
        worlds["holddeg"] = d
        for kind in ["real", "hold"] + CONTROLS + ["holddeg"]:
            wd = worlds[kind]
            A = pipeline(os.path.join(wd, "world.tsv"), os.path.join(base, "run", kind, "main"), seed, "0")
            det = "-"
            if seed == SEEDS[0]:
                Bn = pipeline(os.path.join(wd, "world.tsv"), os.path.join(base, "run", kind, "rerun"), seed, "7")
                C = pipeline(os.path.join(wd, "world_shuffled.tsv"), os.path.join(base, "run", kind, "shuffled"),
                             seed, "3")
                det = "same" if same(A, Bn) and same(A, C) else "DIFF"
            st = stats(os.path.join(A, "selection3.tsv"))
            pr = "-"
            if kind in ("hold", "holddeg"):
                py("predict_real.py", os.path.join(wd, "world.tsv"), os.path.join(A, "selection3.tsv"),
                   os.path.join(hold, "hidden.tsv"), os.path.join(A, "predict.txt"))
                pr = kv(os.path.join(A, "predict.txt"))
            rows.append((seed, kind, st, pr, det))
    lines = ["seed world | U-kept/P-selected | cand pool qcap stable webb_pass | webb_dec withdrawn high_no_plane | "
             "R2: predicted correct transfer_pred transfer_correct | R3"]
    for seed, kind, st, pr, det in rows:
        r2 = "-" if pr == "-" else "%s %s %s %s" % (pr["predicted"], pr["correct"], pr["transfer_predicted"],
                                                      pr["transfer_correct"])
        lines.append("%d %s | %d/%d | %d %d %d %d %d | %d %d %d | %s | %s" % (
            seed, kind, st["universal_kept"], st["selected_planes"], st["candidates"], st["pool"], st["qcap"], st["stable"], st["webb_pass"],
            st["webb_decisive"], st["universal_withdrawn"], st["high_laws_without_plane"], r2, det))
    neg = [r for r in rows if r[1] in CONTROLS]
    # selected laws = kept universal (v2.1 selection kept after withdrawal) + selected planes; read from files
    sel_counts = {}
    for seed, kind, st, pr, det in rows:
        f = os.path.join(OUT, "seed%d" % seed, "run", kind, "main", "selection3.tsv")
        n = 0
        for l in open(f):
            p = l.rstrip("\n").split("\t")
            if p[0] in ("U", "P") and p[-1] == "1":
                n += 1
        sel_counts[(seed, kind)] = n
    lines.append("")
    lines.append("selected (law,plane) per world: " + " ".join(
        "%d:%s=%d" % (s, k, n) for (s, k), n in sorted(sel_counts.items())))
    lines.append("R1 %s" % ("PASS" if all(sel_counts[(r[0], r[1])] == 0 for r in neg) else "FAIL"))
    lines.append("R3 %s" % ("PASS" if all(r[4] in ("same", "-") for r in rows) and
                              all(r[4] == "same" for r in rows if r[0] == SEEDS[0]) else "FAIL"))
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()

"""Entry: whole pipeline for seeds x worlds, then acceptance summary.
usage: python3 run.py [OUTDIR] [SEEDS comma list]   (default out/ , seeds 1,2,3,4,5)"""
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out")
SEEDS = [int(s) for s in (sys.argv[2] if len(sys.argv) > 2 else "1,2,3,4,5").split(",")]
WORLDS = ["A", "twin", "broken", "random"]


def py(script, *args, hashseed="0"):
    env = dict(os.environ, PYTHONHASHSEED=hashseed)
    subprocess.run([sys.executable, "-B", os.path.join(HERE, script), *map(str, args)], check=True,
                   env=env, cwd=HERE, stdout=subprocess.DEVNULL,
                   stderr=None)


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]


def kv(path):
    return dict(l.split("=", 1) for l in open(path).read().splitlines() if "=" in l)


def pipeline(wdir, wfile, seed, tag, hashseed):
    sd = os.path.join(wdir, tag)
    os.makedirs(sd, exist_ok=True)
    w = os.path.join(wdir, wfile)
    py("candidates.py", w, os.path.join(sd, "candidates.tsv"), hashseed=hashseed)
    py("select_laws.py", w, os.path.join(sd, "candidates.tsv"), seed, os.path.join(sd, "selection.tsv"), hashseed=hashseed)
    py("report.py", w, os.path.join(sd, "selection.tsv"), os.path.join(sd, "report.txt"),
       os.path.join(sd, "exceptions.tsv"), hashseed=hashseed)
    oracle = os.path.join(wdir, "oracle.tsv")
    py("score.py", oracle if os.path.exists(oracle) else "-", os.path.join(sd, "selection.tsv"),
       os.path.join(sd, "exceptions.tsv"), os.path.join(sd, "score.txt"), hashseed=hashseed)
    return sd


def main():
    rows, lines = [], []
    for seed in SEEDS:
        base = os.path.join(OUT, "seed%d" % seed)
        for kind in WORLDS:
            wdir = os.path.join(base, kind)
            args = [kind, seed, wdir] + ([os.path.join(base, "A")] if kind in ("twin", "broken") else [])
            py("gen_world.py", *args)
            a = pipeline(wdir, "world.tsv", seed, "main", "0")
            b = pipeline(wdir, "world.tsv", seed, "rerun", "7")  # other hash seed, same input
            c = pipeline(wdir, "world_shuffled.tsv", seed, "shuffled", "3")  # row permutation
            same = all(sha(os.path.join(a, f)) == sha(os.path.join(x, f))
                       for x in (b, c) for f in ("candidates.tsv", "selection.tsv", "report.txt", "exceptions.tsv", "score.txt"))
            sc = kv(os.path.join(a, "score.txt"))
            st = {l.split("\t")[1]: int(l.split("\t")[2]) for l in open(os.path.join(a, "selection.tsv"))
                  if l.startswith("#stat")}
            rows.append((seed, kind, sc, st, same))
    lines.append("seed world selected true_exact true_exc false designed nondesigned exc_listed exc_real "
                 "c1 only_twin only_hold derivable_blocked deterministic")
    for seed, kind, sc, st, same in rows:
        lines.append("%d %s %s %s %s %s %s %s %s %s %d %d %d %d %s" % (
            seed, kind, sc["selected"], sc.get("true_exact", "-"), sc.get("true_with_exceptions", "-"),
            sc.get("false_selected", "-"), sc.get("designed_selected", "-"), sc.get("nondesigned_selected", "-"),
            sc.get("exceptions_listed", "-"), sc.get("exceptions_real_violations", "-"),
            st["c1"], st["only_twin_blocks"], st["only_holdout_blocks"], st["derivable_blocked"], same))
    A = [r for r in rows if r[1] == "A"]
    neg = [r for r in rows if r[1] != "A"]
    p1 = all(int(r[2]["false_selected"]) == 0 for r in A)
    p2 = all(int(r[2]["true_with_exceptions"]) >= 1 and int(r[2]["exceptions_listed"]) > 0 for r in A)
    p3 = all(int(r[2]["selected"]) == 0 for r in neg)
    p4 = all(r[4] for r in rows)
    lines += ["", "P1 selected subset of true (world A, all seeds): %s" % ("PASS" if p1 else "FAIL"),
              "P2 true law with listed exceptions selected (world A, all seeds): %s" % ("PASS" if p2 else "FAIL"),
              "P3 zero selected on all negative worlds: %s" % ("PASS" if p3 else "FAIL"),
              "P4 byte-identical (permutation, rerun, hashseed): %s" % ("PASS" if p4 else "FAIL")]
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()

"""Entry v3: worlds A2/twin/broken/random/degtwin x seeds; v2.1 stage, then the plane stage (H115).
usage: python3 run_v3.py [OUTDIR] [SEEDS comma list]  (default out_v3/, seeds 1..5). EXC_CODE=binom forced.
Outputs per world: v21/<tag>/..., v3/<tag>/...; summary in OUTDIR/summary.txt."""
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out_v3")
SEEDS = [int(s) for s in (sys.argv[2] if len(sys.argv) > 2 else "1,2,3,4,5").split(",")]
WORLDS = ["A2", "twin", "broken", "random", "degtwin"]
F21 = ("candidates.tsv", "selection.tsv", "report.txt", "exceptions.tsv", "score.txt")
F3 = ("selection3.tsv", "report3.txt", "exceptions3.tsv", "score3.txt")


def py(script, *args, hashseed="0"):
    env = dict(os.environ, PYTHONHASHSEED=hashseed, EXC_CODE="binom")
    subprocess.run([sys.executable, "-B", os.path.join(HERE, script), *map(str, args)], check=True,
                   env=env, cwd=HERE, stdout=subprocess.DEVNULL)


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]


def kv(path):
    return dict(l.split("=", 1) for l in open(path).read().splitlines() if "=" in l)


def stats(path):
    st = {}
    for l in open(path):
        p = l.rstrip("\n").split("\t")
        if p[0] == "#stat":
            st[p[1]] = int(p[2])
        elif p[0] == "#info":
            st["info"] = " ".join(p[1:])
    return st


def pipeline(wdir, wfile, seed, tag, hashseed):
    w = os.path.join(wdir, wfile)
    d21, d3 = os.path.join(wdir, "v21", tag), os.path.join(wdir, "v3", tag)
    os.makedirs(d21, exist_ok=True)
    os.makedirs(d3, exist_ok=True)
    cand, sel21 = os.path.join(d21, "candidates.tsv"), os.path.join(d21, "selection.tsv")
    sel3 = os.path.join(d3, "selection3.tsv")
    oracle = os.path.join(wdir, "oracle.tsv")
    orc = oracle if os.path.exists(oracle) else "-"
    py("candidates.py", w, cand, hashseed=hashseed)
    py("select_stability.py", w, cand, seed, sel21, hashseed=hashseed)
    py("report.py", w, sel21, os.path.join(d21, "report.txt"), os.path.join(d21, "exceptions.tsv"), hashseed=hashseed)
    py("score.py", orc, sel21, os.path.join(d21, "exceptions.tsv"), os.path.join(d21, "score.txt"), hashseed=hashseed)
    py("select_plane.py", w, cand, sel21, seed, sel3, hashseed=hashseed)
    py("report3.py", w, sel3, os.path.join(d3, "report3.txt"), os.path.join(d3, "exceptions3.tsv"), hashseed=hashseed)
    py("score3.py", orc, sel3, os.path.join(d3, "score3.txt"), hashseed=hashseed)
    return d21, d3


def main():
    rows = []
    for seed in SEEDS:
        base = os.path.join(OUT, "seed%d" % seed)
        for kind in WORLDS:
            wdir = os.path.join(base, kind)
            args = [kind, seed, wdir] + ([os.path.join(base, "A2")] if kind in ("twin", "broken", "degtwin") else [])
            py("gen_world2.py", *args)
            A = pipeline(wdir, "world.tsv", seed, "main", "0")
            Bn = pipeline(wdir, "world.tsv", seed, "rerun", "7")
            C = pipeline(wdir, "world_shuffled.tsv", seed, "shuffled", "3")
            same21 = all(sha(os.path.join(A[0], f)) == sha(os.path.join(x[0], f)) for x in (Bn, C) for f in F21)
            same3 = all(sha(os.path.join(A[1], f)) == sha(os.path.join(x[1], f)) for x in (Bn, C) for f in F3)
            rows.append((seed, kind, kv(os.path.join(A[0], "score.txt")), kv(os.path.join(A[1], "score3.txt")),
                         stats(os.path.join(A[1], "selection3.tsv")), same21, same3))
    lines = ["seed world | v21: selected false | v3: selected(U/P) true_in_plane false tight boundary_tight "
             "one_sex sex_proxy rel_in_rhs | pool qcap stable webb_pass stab_dec webb_dec withdrawn high_no_plane | det21 det3"]
    for seed, kind, s21, s3, st, d21, d3 in rows:
        lines.append("%d %s | %s %s | %s(%s/%s) %s %s %s %s %s %s %s | %s %s %s %s %s %s %s %s | %s %s" % (
            seed, kind, s21["selected"], s21.get("false_selected", "-"),
            s3["selected"], s3["selected_universal"], s3["selected_planes"], s3.get("true_in_plane", "-"),
            s3.get("false_in_plane", "-"), s3.get("tight_planes_le_third", "-"),
            s3.get("boundary_laws_with_tight_plane", "-"), s3.get("plane_one_sex", "-"),
            s3.get("sex_proxy_planes", "-"), s3.get("cond_rel_in_rhs", "-"),
            st.get("pool", "-"), st.get("qcap", "-"), st.get("stable", "-"), st.get("webb_pass", "-"),
            st.get("stability_decisive", "-"), st.get("webb_decisive", "-"), st.get("universal_withdrawn", "-"),
            st.get("high_laws_without_plane", "-"), d21, d3))
    A2 = [r for r in rows if r[1] == "A2"]
    neg = [r for r in rows if r[1] != "A2"]
    lines.append("")
    lines.append("[v2.1] P1 %s | P2 %s | P3 %s | P4 %s" % (
        *("PASS" if x else "FAIL" for x in (
            all(int(r[2]["false_selected"]) == 0 for r in A2),
            all(int(r[2]["true_with_exceptions"]) >= 1 for r in A2),
            all(int(r[2]["selected"]) == 0 for r in neg),
            all(r[5] for r in rows))),))
    lines.append("[v3]   P1' %s | P2' %s (%d/%d seeds) | P3 %s | P4 %s" % (
        "PASS" if all(int(r[3]["false_in_plane"]) == 0 for r in A2) else "FAIL",
        "PASS" if all(int(r[3]["boundary_laws_with_tight_plane"]) >= 1 for r in A2) else "FAIL",
        sum(int(r[3]["boundary_laws_with_tight_plane"]) >= 1 for r in A2), len(A2),
        "PASS" if all(int(r[3]["selected"]) == 0 for r in neg) else "FAIL",
        "PASS" if all(r[5] and r[6] for r in rows) else "FAIL"))
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()

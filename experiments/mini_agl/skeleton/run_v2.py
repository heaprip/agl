"""Entry v2: worlds A2/twin/broken/random/degtwin x seeds x rules (v1 rule, v2.1).
usage: python3 run_v2.py [OUTDIR] [SEEDS comma list]   (default out_v2/, seeds 1..5). EXC_CODE=binom forced."""
import hashlib
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "out_v2")
SEEDS = [int(s) for s in (sys.argv[2] if len(sys.argv) > 2 else "1,2,3,4,5").split(",")]
WORLDS = ["A2", "twin", "broken", "random", "degtwin"]
RULES = ["v1rule", "v2"]
FILES = ("candidates.tsv", "selection.tsv", "report.txt", "exceptions.tsv", "score.txt")


def py(script, *args, hashseed="0"):
    env = dict(os.environ, PYTHONHASHSEED=hashseed, EXC_CODE="binom")
    subprocess.run([sys.executable, "-B", os.path.join(HERE, script), *map(str, args)], check=True,
                   env=env, cwd=HERE, stdout=subprocess.DEVNULL)


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]


def kv(path):
    return dict(l.split("=", 1) for l in open(path).read().splitlines() if "=" in l)


def pipeline(wdir, wfile, seed, tag, hashseed):
    """Runs both rules on one input; returns {rule: dir}."""
    w = os.path.join(wdir, wfile)
    dirs = {}
    for rule in RULES:
        dirs[rule] = os.path.join(wdir, rule, tag)
        os.makedirs(dirs[rule], exist_ok=True)
        py("candidates.py", w, os.path.join(dirs[rule], "candidates.tsv"), hashseed=hashseed)
    cand = lambda r: os.path.join(dirs[r], "candidates.tsv")  # noqa: E731
    sel = lambda r: os.path.join(dirs[r], "selection.tsv")  # noqa: E731
    py("select_laws.py", w, cand("v1rule"), seed, sel("v1rule"), hashseed=hashseed)
    py("select_stability.py", w, cand("v2"), seed, sel("v2"), hashseed=hashseed)
    for rule in RULES:
        finish(wdir, w, dirs[rule], hashseed)
    return dirs


def finish(wdir, w, sd, hashseed):
    sel = os.path.join(sd, "selection.tsv")
    py("report.py", w, sel, os.path.join(sd, "report.txt"), os.path.join(sd, "exceptions.tsv"), hashseed=hashseed)
    oracle = os.path.join(wdir, "oracle.tsv")
    py("score.py", oracle if os.path.exists(oracle) else "-", sel, os.path.join(sd, "exceptions.tsv"),
       os.path.join(sd, "score.txt"), hashseed=hashseed)


def stats(sel):
    st = {}
    for l in open(sel):
        p = l.rstrip("\n").split("\t")
        if p[0] == "#stat":
            st[p[1]] = int(p[2])
        elif p[0] == "#info":
            st["info"] = " ".join(p[1:])
    return st


def main():
    rows = []
    for seed in SEEDS:
        base = os.path.join(OUT, "seed%d" % seed)
        for kind in WORLDS:
            wdir = os.path.join(base, kind)
            args = [kind, seed, wdir] + ([os.path.join(base, "A2")] if kind in ("twin", "broken", "degtwin") else [])
            py("gen_world2.py", *args)
            A_, B_, C_ = (pipeline(wdir, "world.tsv", seed, "main", "0"),
                          pipeline(wdir, "world.tsv", seed, "rerun", "7"),
                          pipeline(wdir, "world_shuffled.tsv", seed, "shuffled", "3"))
            for rule in RULES:
                a, b, c = A_[rule], B_[rule], C_[rule]
                same = all(sha(os.path.join(a, f)) == sha(os.path.join(x, f)) for x in (b, c) for f in FILES)
                rows.append((seed, kind, rule, kv(os.path.join(a, "score.txt")),
                             stats(os.path.join(a, "selection.tsv")), same))
    lines = ["seed world rule selected true_exact true_exc false designed nondesigned exc_share(min-max) "
             "c1 stable webb_pass stab_decisive webb_decisive deriv_blocked qcap det | info"]
    for seed, kind, rule, sc, st, same in rows:
        sh = "-"
        if "truth" in sc and sc["truth"]:
            v = [(int(a), int(b)) for a, b in re.findall(r":(\d+)/(\d+)", sc["truth"])]
            fr = [m / n for m, n in v if n]
            sh = "%.2f-%.2f" % (min(fr), max(fr)) if fr else "-"
        lines.append("%d %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s %s | %s" % (
            seed, kind, rule, sc["selected"], sc.get("true_exact", "-"), sc.get("true_with_exceptions", "-"),
            sc.get("false_selected", "-"), sc.get("designed_selected", "-"), sc.get("nondesigned_selected", "-"), sh,
            st.get("c1", "-"), st.get("stable", "-"), st.get("webb_pass", "-"), st.get("stability_decisive", "-"),
            st.get("webb_decisive", "-"), st.get("derivable_blocked", "-"), st.get("qcap", "-"), same,
            st.get("info", "-")))
    lines.append("")
    for rule in RULES:
        A = [r for r in rows if r[1] == "A2" and r[2] == rule]
        neg = [r for r in rows if r[1] != "A2" and r[2] == rule]
        every = [r for r in rows if r[2] == rule]
        p1 = all(int(r[3]["false_selected"]) == 0 for r in A)
        p2 = all(int(r[3]["true_with_exceptions"]) >= 1 and int(r[3]["exceptions_listed"]) > 0 for r in A)
        p3 = all(int(r[3]["selected"]) == 0 for r in neg)
        p4 = all(r[5] for r in every)
        lines += ["[%s] P1 %s | P2 %s | P3 %s | P4 %s" % (rule, "PASS" if p1 else "FAIL", "PASS" if p2 else "FAIL",
                                                           "PASS" if p3 else "FAIL", "PASS" if p4 else "FAIL")]
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, "summary.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()

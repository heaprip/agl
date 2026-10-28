"""Enumerate size-bounded inclusions T1 <= T2 over observed relations (QuickSpec-style).
usage: candidates.py WORLD CANDIDATES. Uses the finding half of the records only (see split)."""
import hashlib
import sys

from lawlib import World, canon_law, eval_term, inv_atom, law_str, read_world, saving


def split(recs):
    """Per relation, records ranked by hash of id: even ranks find, odd ranks hold out."""
    find, hold = {}, {}
    for rel in sorted({r["rel"] for r in recs.values()}):
        ids = sorted((i for i in recs if recs[i]["rel"] == rel),
                     key=lambda i: hashlib.sha256(i.encode()).hexdigest())
        for k, i in enumerate(ids):
            (find if k % 2 == 0 else hold)[i] = recs[i]
    return find, hold


def enumerate_candidates(w):
    atoms = [a for rel in w.rels for a in (rel, inv_atom(rel))]
    terms = [(a,) for a in atoms] + [(a, b) for a in atoms for b in atoms]
    seen = set()
    for t1 in terms:
        for t2 in terms:
            if t1 == t2 or (len(t1) > 1 and len(t2) > 1):
                continue
            law = canon_law(t1, t2)
            if law in seen:
                continue
            seen.add(law)
    return sorted(seen, key=lambda l: law_str(*l))


def main():
    recs = read_world(sys.argv[1])
    find, _ = split(recs)
    w = World(find)
    out = []
    for t1, t2 in enumerate_candidates(w):
        if not eval_term(w, t1) or not eval_term(w, t2):
            continue
        s = saving(w, t1, t2)
        if s is None:
            continue
        out.append("%s\t%d\t%d" % (law_str(t1, t2), len(eval_term(w, t1)), len(eval_term(w, t2))))
    with open(sys.argv[2], "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()

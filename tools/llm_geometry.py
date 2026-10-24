#!/usr/bin/env python3
"""Concept vectors of open LLMs against WordNet labels (docs/hypotheses.md, H62).

    tools/llm_geometry.py fetch [MODEL...]   download the output matrix and tokenizer
                                             of each pinned Qwen2.5 model into data/cache/llm/
                                             (outside git) and write data/llm/MANIFEST
    uv run --python 3.12 --with numpy==2.2.6 tools/llm_geometry.py run [MODEL...]
                                             offline: check MANIFEST, measure, write
                                             data/llm/results.json and print the tables

The model is never run. Park et al. ("The Geometry of Categorical and
Hierarchical Concepts in Large Language Models", ICLR 2025, arXiv 2406.01506)
estimate concept vectors from the unembedding matrix alone, and only that
matrix is downloaded, by HTTP range requests into the safetensors file at a
pinned revision: for 0.5B and 1.5B it is the input embedding (tied), for the
larger models `lm_head.weight` in the last shard.

Method (as in the paper; the differences are listed in H62):
  - whitening g(y) = Cov(γ)^(-1/2) (γ(y) - E γ) over the whole vocabulary of
    the tokenizer (rows past it are padding and are left out);
  - words of a WordNet noun synset: lemmas of the synset and of all its
    descendants (hypernym and instance hypernym), as written, lowercase and
    capitalized, kept if " word" is one token; concepts with >= 50 tokens;
  - ℓ̄_w = (g̃ᵀ E g_w) g̃, g̃ ∝ Cov(g_w)^(-1) E g_w, the covariance shrunk by
    the Ledoit-Wolf formula and estimated on at most 2000 words drawn from
    the seed; the mean is over all training words.

Checks, per model and seed, each concept split 70/30 by the seed:
  1. existence: mean projection g·ℓ̄/|ℓ̄|² of held-out words (~1) and of as
     many random words outside the concept (~0): words of WordNet and EXTRA
     alphabetic tokens outside it, drawn once from seed 0;
  2. orthogonality: cos(ℓ̄_genus, ℓ̄_species - ℓ̄_genus) for direct pairs,
     each fitted on its own 70 % (so the species words are not a subset of
     the genus words), against a random "genus": a concept that is neither
     ancestor nor descendant of the species;
  3. two genera: share of |ℓ̄_species| in the plane of both genera, against
     the plane of one genus and a random concept.
  2b (added after the noise control showed that check 2 passes with no
     model): the genus fitted on its words without the species' words,
     where at least MIN_WORDS remain. Both 2 and 2b are also compared with
     a random genus of about the same word count (one of the 5 nearest), since
     with no model the cosine depends on the ratio of word counts alone.

`run noise` repeats the checks on a control added after the declaration: the
0.5B vocabulary with random Gaussian rows instead of the model.

Randomness comes from the seed and the concept's rank in id order, so the
result does not depend on the order of the data. Matrix products run in
parallel BLAS, so the last digits may vary; the tables round them.

Data: Qwen2.5 (Apache 2.0, except 72B: Qwen license), https://huggingface.co/Qwen.
Open English WordNet 2025-plus (CC BY 4.0), from data/onto/raw (tools/onto_stats.py).

`fetch` uses the standard library only; `run` needs numpy.
"""

import gzip
import hashlib
import json
import pathlib
import struct
import sys
import urllib.request

import onto_stats

ROOT = pathlib.Path(__file__).resolve().parent.parent
CACHE = ROOT / "data" / "cache" / "llm"
OUT = ROOT / "data" / "llm"
MANIFEST = OUT / "MANIFEST"
RESULTS = OUT / "results.json"
WORDNET = "english-wordnet-2025-plus.xml.gz"

# Name -> (revision, shard, tensor, rows, columns). Checked against the
# shard header on fetch.
MODELS = {
    "0.5B": ("060db6499f32faf8b98477b0a26969ef7d8b9987", "model.safetensors",
             "model.embed_tokens.weight", 151936, 896),
    "1.5B": ("8faed761d45a263340a0528343f099c05c9a4323", "model.safetensors",
             "model.embed_tokens.weight", 151936, 1536),
    "7B": ("d149729398750b98c0af14eb82c78cfe92750796", "model-00004-of-00004.safetensors",
           "lm_head.weight", 152064, 3584),
    "32B": ("1818d35814b8319459f4bd55ed1ac8709630f003", "model-00017-of-00017.safetensors",
            "lm_head.weight", 152064, 5120),
    "72B": ("efba10c8e54e91e0d9570ab5f7b51a958474d4cb", "model-00037-of-00037.safetensors",
            "lm_head.weight", 152064, 8192),
}
SEEDS = (1, 2)
# Not a model: the 0.5B tokenizer with Gaussian rows drawn from seed 0. Shows
# what the estimator and the nesting of word sets give with no model at all.
CONTROL = "noise"
MIN_WORDS = 50
MAX_COV = 2000
EXTRA = 10000
TRAIN = 0.7


def url(model, name):
    rev = MODELS[model][0]
    return f"https://huggingface.co/Qwen/Qwen2.5-{model}/resolve/{rev}/{name}"


def get(u, start=None, end=None):
    headers = {"Range": f"bytes={start}-{end}"} if start is not None else {}
    with urllib.request.urlopen(urllib.request.Request(u, headers=headers), timeout=300) as r:
        return r.read()


def fetch_range(u, path, start, length):
    """Stream bytes [start, start + length) into path, resuming a partial file."""
    part = path.with_suffix(".part")
    have = part.stat().st_size if part.exists() else 0
    with open(part, "ab") as f:
        while have < length:
            end = min(length, have + (64 << 20)) - 1
            chunk = get(u, start + have, start + end)
            if len(chunk) != end - have + 1:
                raise SystemExit(f"{u}: short read at {have}")
            f.write(chunk)
            have += len(chunk)
            print(f"\r{path.name}: {have >> 20} / {length >> 20} MB", end="", flush=True)
    print()
    part.rename(path)


def fetch(models):
    CACHE.mkdir(parents=True, exist_ok=True)
    OUT.mkdir(parents=True, exist_ok=True)
    for m in models:
        _, shard, tensor, rows, cols = MODELS[m]
        tok = CACHE / f"qwen2.5-{m}.tokenizer.json"
        if not tok.exists():
            tok.write_bytes(get(url(m, "tokenizer.json")))
        mat = CACHE / f"qwen2.5-{m}.{tensor}.bf16"
        if mat.exists():
            continue
        n = struct.unpack("<Q", get(url(m, shard), 0, 7))[0]
        info = json.loads(get(url(m, shard), 8, 8 + n - 1))[tensor]
        lo, hi = info["data_offsets"]
        if info["dtype"] != "BF16" or info["shape"] != [rows, cols] or hi - lo != rows * cols * 2:
            raise SystemExit(f"{m}: header {info} does not match the pinned shape")
        fetch_range(url(m, shard), mat, 8 + n + lo, hi - lo)
    files = sorted(p for p in CACHE.iterdir() if p.is_file() and p.suffix != ".part")
    MANIFEST.write_text("".join(f"{sha256(p)}  {p.name}\n" for p in files))
    print(f"{len(files)} files")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while b := f.read(1 << 24):
            h.update(b)
    return h.hexdigest()


def verified(models):
    pinned = dict(reversed(line.split("  ", 1)) for line in MANIFEST.read_text().splitlines())
    for m in models:
        for name in (f"qwen2.5-{m}.tokenizer.json", f"qwen2.5-{m}.{MODELS[m][2]}.bf16"):
            if name not in pinned or sha256(CACHE / name) != pinned[name]:
                raise SystemExit(f"{name}: missing or does not match MANIFEST")


def byte_chars():
    """GPT-2 byte-level BPE: each byte is written as a printable character."""
    bs = list(range(33, 127)) + list(range(161, 173)) + list(range(174, 256))
    cs = bs[:]
    n = 0
    for b in range(256):
        if b not in bs:
            bs.append(b)
            cs.append(256 + n)
            n += 1
    return dict(zip(bs, map(chr, cs)))


def load_vocab(m):
    tok = json.loads((CACHE / f"qwen2.5-{m}.tokenizer.json").read_text(encoding="utf-8"))
    return tok["model"]["vocab"]


def load_wordnet():
    """Noun synsets of OEWN 2025-plus: id -> (genera, lemmas), in id order."""
    import xml.etree.ElementTree as ET

    lemmas, genera = {}, {}
    with gzip.open(onto_stats.RAW / WORDNET) as f:
        for _, el in ET.iterparse(f):
            if el.tag == "LexicalEntry":
                lemma = el.find("Lemma")
                if lemma.get("partOfSpeech") == "n":
                    for s in el.iter("Sense"):
                        lemmas.setdefault(s.get("synset"), set()).add(lemma.get("writtenForm"))
                el.clear()
            elif el.tag == "Synset":
                if el.get("partOfSpeech") == "n":
                    genera[el.get("id")] = {
                        r.get("target") for r in el.iter("SynsetRelation")
                        if r.get("relType") in ("hypernym", "instance_hypernym")}
                el.clear()
    return {k: (sorted(g for g in genera[k] if g in genera), sorted(lemmas.get(k, ())))
            for k in sorted(genera)}


def concept_tokens(wn, vocab):
    """Synset -> sorted token ids of its own and its descendants' lemmas."""
    enc = byte_chars()

    def ids(word):
        out = set()
        for form in {word, word.lower(), word.lower().capitalize()}:
            t = "Ġ" + "".join(enc[b] for b in form.encode("utf-8"))
            if t in vocab:
                out.add(vocab[t])
        return out

    children = {k: [] for k in wn}
    for k, (gen, _) in wn.items():
        for g in gen:
            children[g].append(k)
    own = {k: set().union(*map(ids, lem)) if lem else set() for k, (_, lem) in wn.items()}
    memo = {}
    sys.setrecursionlimit(100000)

    def go(k):
        if k not in memo:
            s = set(own[k])
            for c in children[k]:
                s |= go(c)
            memo[k] = s
        return memo[k]

    return {k: sorted(go(k)) for k in wn}


def ancestors(wn):
    memo = {}

    def go(k):
        if k not in memo:
            s = set()
            for g in wn[k][0]:
                s.add(g)
                s |= go(g)
            memo[k] = s
        return memo[k]

    return {k: go(k) for k in wn}


def run(models):
    import numpy as np

    np.seterr(all="ignore")  # spurious with Accelerate; see fit()
    onto_stats.verified()
    verified([m for m in models if m != CONTROL])
    wn = load_wordnet()
    anc = ancestors(wn)
    results = json.loads(RESULTS.read_text()) if RESULTS.exists() else {}
    for m in models:
        vocab = load_vocab("0.5B" if m == CONTROL else m)
        rows, cols = MODELS["0.5B" if m == CONTROL else m][3:]
        nv = len(vocab)
        toks = concept_tokens(wn, vocab)
        concepts = [k for k in wn if len(toks[k]) >= MIN_WORDS]
        rank = {k: i for i, k in enumerate(concepts)}
        words = set().union(*(toks[k] for k in concepts))
        # Random words also come from outside WordNet: the root covers all of it.
        outside = sorted(i for t, i in vocab.items()
                         if i not in words and t[:1] == "Ġ" and t[1:].isalpha())
        extra = np.random.default_rng(0).choice(len(outside), EXTRA, replace=False)
        needed = sorted(words | {outside[i] for i in extra})
        print(f"== {m}: d {cols}, vocab {nv}, concepts {len(concepts)}, words {len(words)}",
              flush=True)

        if m == CONTROL:
            noise = np.random.default_rng(0).standard_normal((rows, cols), dtype=np.float32)

            def rows_f32(sel):
                return noise[sel]
        else:
            raw = np.memmap(CACHE / f"qwen2.5-{m}.{MODELS[m][2]}.bf16", dtype=np.uint16,
                            mode="r", shape=(rows, cols))

            def rows_f32(sel):
                return (np.asarray(raw[sel], dtype=np.uint32) << 16).view(np.float32)

        # Whitening over the tokenizer vocabulary.
        mean = np.zeros(cols)
        gram = np.zeros((cols, cols))
        for a in range(0, nv, 8192):
            x = rows_f32(slice(a, min(nv, a + 8192))).astype(np.float64)
            mean += x.sum(0)
            gram += x.T @ x
        mean /= nv
        cov = gram / nv - np.outer(mean, mean)
        lam, u = np.linalg.eigh(cov)
        if lam[0] <= 0:
            raise SystemExit(f"{m}: covariance of the vocabulary is singular")
        whiten = (u / np.sqrt(lam)) @ u.T
        pos = {t: i for i, t in enumerate(needed)}
        g = ((rows_f32(np.array(needed)).astype(np.float64) - mean) @ whiten).astype(np.float32)
        if not np.isfinite(g).all():
            raise SystemExit(f"{m}: whitened vectors are not finite")
        del gram, cov, u

        results[m] = {}
        for seed in SEEDS:
            vec, held, rand_proj = {}, {}, {}
            for k in concepts:
                rng = np.random.default_rng([seed, rank[k]])
                idx = np.array([pos[t] for t in toks[k]])
                rng.shuffle(idx)
                cut = int(round(TRAIN * len(idx)))
                train, test = idx[:cut], idx[cut:]
                vec[k] = fit(np, g[train], rng)
                l2 = float(vec[k] @ vec[k])
                other = np.ones(len(needed), bool)
                other[idx] = False
                rnd = rng.choice(np.flatnonzero(other), size=len(test), replace=False)
                held[k] = float((g[test] @ vec[k]).mean() / l2)
                rand_proj[k] = float((g[rnd] @ vec[k]).mean() / l2)
            res = {"concepts": len(concepts), "words": len(words),
                   "held": quant(held.values()), "random": quant(rand_proj.values())}

            def cos(a, b):
                return float(a @ b / np.linalg.norm(a) / np.linalg.norm(b))

            true, fake, sized, apart, apart_sized = [], [], [], [], []
            size = {k: len(toks[k]) for k in concepts}

            def like(n, pool, rng):
                # A random one of the 5 concepts nearest in word count.
                near = sorted(pool, key=lambda c: (abs(np.log(size[c] / n)), rank[c]))[:5]
                return near[rng.integers(len(near))]
            pairs, doubles = 0, []
            for k in concepts:
                rng = np.random.default_rng([seed, rank[k], 1])
                unrelated = [c for c in concepts if c != k and c not in anc[k] and k not in anc[c]]
                for p in wn[k][0]:
                    pairs += 1
                    r = unrelated[rng.integers(len(unrelated))]
                    true.append(cos(vec[p], vec[k] - vec[p]))
                    fake.append(cos(vec[r], vec[k] - vec[r]))
                    r = like(size[p], unrelated, rng)
                    sized.append(cos(vec[r], vec[k] - vec[r]))
                    # 2b: the genus fitted on its words without the species' words.
                    own = set(toks[k])
                    rest = np.array([pos[t] for t in toks[p] if t not in own])
                    if len(rest) >= MIN_WORDS:
                        r2 = np.random.default_rng([seed, rank[p], rank[k]])
                        r2.shuffle(rest)
                        v = fit(np, g[rest[:int(round(TRAIN * len(rest)))]], r2)
                        apart.append(cos(v, vec[k] - v))
                        r = like(len(rest), unrelated, rng)
                        apart_sized.append(cos(vec[r], vec[k] - vec[r]))
                if len(wn[k][0]) == 2:
                    p1, p2 = wn[k][0]
                    r = unrelated[rng.integers(len(unrelated))]
                    doubles.append((share(np, vec[k], [vec[p1]]), share(np, vec[k], [vec[p2]]),
                                    share(np, vec[k], [vec[p1], vec[p2]]),
                                    share(np, vec[k], [vec[p1], vec[r]])))
            res.update({"pairs": pairs, "cos_true": quant(true), "cos_random": quant(fake),
                        "nearer_orthogonal": nearer(np, true, fake),
                        "cos_random_sized": quant(sized),
                        "nearer_orthogonal_sized": nearer(np, true, sized),
                        "pairs_apart": len(apart), "cos_apart": quant(apart),
                        "cos_apart_random_sized": quant(apart_sized),
                        "nearer_orthogonal_apart": nearer(np, apart, apart_sized),
                        "two_genera": len(doubles)})
            if doubles:
                d = np.array(doubles)
                res.update({"share_genus1": quant(d[:, 0]), "share_genus2": quant(d[:, 1]),
                            "share_both": quant(d[:, 2]), "share_genus_random": quant(d[:, 3])})
            results[m][str(seed)] = res
            print(json.dumps({"model": m, "seed": seed, **res}, ensure_ascii=False), flush=True)
        RESULTS.write_text(json.dumps(results, indent=1, ensure_ascii=False) + "\n")


def fit(np, x, rng):
    """ℓ̄ = (g̃ᵀ μ) g̃, g̃ ∝ Σ⁻¹ μ, Σ shrunk by Ledoit-Wolf on at most MAX_COV rows.

    numpy with Apple Accelerate raises spurious floating-point warnings in
    matmul; they are silenced and the result is checked for finiteness instead.
    """
    mu = x.mean(0).astype(np.float64)
    s = x if len(x) <= MAX_COV else x[np.sort(rng.choice(len(x), MAX_COV, replace=False))]
    s = s.astype(np.float64)
    s = s - s.mean(0)
    n, d = s.shape
    gram = s @ s.T
    sq = np.diag(gram)
    tr = sq.sum() / n
    m = tr / d
    fro = (gram ** 2).sum() / n ** 2
    delta = (fro - d * m * m) / d
    beta = min(delta, ((sq ** 2).sum() / n ** 2 - fro / n) / d)
    a = beta / delta
    if a >= 1:
        # Full shrinkage: Σ = m I, so g̃ ∝ μ (happens with no structure, as in the control).
        w = mu.copy()
    elif n > d:
        sigma = (1 - a) * (s.T @ s) / n + a * m * np.eye(d)
        w = np.linalg.solve(sigma, mu)
    else:
        # Woodbury: (a m I + (1 - a)/n sᵀs)⁻¹ μ.
        c = n * a * m / (1 - a)
        w = (mu - s.T @ np.linalg.solve(c * np.eye(n) + gram, s @ mu)) / (a * m)
    w /= np.linalg.norm(w)
    if not np.isfinite(w).all():
        raise SystemExit("concept vector is not finite")
    return ((w @ mu) * w).astype(np.float32)


def nearer(np, true, fake):
    """Share of (true, random) pairs where the true cosine is nearer zero."""
    if not true:
        return None
    ft = np.sort(np.abs(fake))
    return round(float(np.mean([len(ft) - np.searchsorted(ft, abs(t), side="right")
                                for t in true])) / len(ft), 3)


def share(np, v, basis):
    q, _ = np.linalg.qr(np.stack(basis, 1).astype(np.float64))
    return float(np.linalg.norm(q.T @ v) / np.linalg.norm(v))


def quant(xs):
    xs = sorted(xs)
    if not xs:
        return None
    return {p: round(float(xs[min(len(xs) - 1, len(xs) * q // 100)]), 3)
            for p, q in (("p10", 10), ("p50", 50), ("p90", 90))}


if __name__ == "__main__":
    cmd, *names = sys.argv[1:] or ["help"]
    names = names or list(MODELS)
    if cmd == "fetch":
        fetch(names)
    elif cmd == "run":
        run(names)
    else:
        print(__doc__)

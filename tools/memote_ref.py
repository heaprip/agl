#!/usr/bin/env python3
"""memote as a differential acceptance test (docs/hypotheses.md, H38).

    tools/memote_ref.py fetch    download the BiGG model into data/bigg/ and write its MANIFEST
    tools/memote_ref.py build    write cases/memote/*.agl from data/bigg/, offline

`build` needs cobra and memote, which the kernel never does:

    uv run --python 3.11 --with memote==0.17.0 --with cobra==0.32.1 tools/memote_ref.py build

For the model and for each seeded mutant it writes one case: the model as
facts, and memote's own verdicts as expectations. The rules that must reproduce
those verdicts are hand-written in cases/memote/rules.agl. Two builds give the
same bytes.

Translated: mass balance, charge balance (internal reactions only, as memote),
orphan, dead-end and disconnected metabolites. Not translated: everything that
needs linear programming (stoichiometric consistency, energy-generating cycles,
blocked reactions, biomass production).
"""

import hashlib
import pathlib
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
RAW = ROOT / "data" / "bigg"
OUT = ROOT / "cases" / "memote"
MODEL = "e_coli_core"
URL = f"http://bigg.ucsd.edu/static/models/{MODEL}.xml"
MUTANTS = 28
SEED = 20261023


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch():
    RAW.mkdir(parents=True, exist_ok=True)
    path = RAW / f"{MODEL}.xml"
    with urllib.request.urlopen(URL, timeout=120) as r:
        path.write_bytes(r.read())
    (RAW / "MANIFEST").write_text(f"{sha(path)}  {path.name}\n")


def verified_model_path():
    path = RAW / f"{MODEL}.xml"
    for line in (RAW / "MANIFEST").read_text().splitlines():
        digest, name = line.split()
        if (RAW / name).exists() and sha(RAW / name) != digest:
            sys.exit(f"hash mismatch: {name}")
    return path


class SplitMix64:
    """Same generator as src/sim.rs, so the mutants do not depend on Python's random."""

    def __init__(self, seed):
        self.s = seed & 0xFFFFFFFFFFFFFFFF

    def next(self):
        self.s = (self.s + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)

    def pick(self, xs):
        return xs[self.next() % len(xs)]


def write_backward(r):
    """The same reaction written right to left: verdicts must not change."""
    lo, up = r.bounds
    r.add_metabolites({m: -2 * c for m, c in r.metabolites.items()})
    r.bounds = (-up, -lo)


def mutate(model, kind, rng):
    """Applies one mutation of the given kind; returns its description."""
    from memote.support import consistency_helpers as H

    by_id = lambda xs: sorted(xs, key=lambda x: x.id)
    internal = by_id(H.get_internals(model))
    mets = by_id(model.metabolites)
    if kind == "drop_participant":
        r = rng.pick([r for r in internal if len(r.metabolites) > 2])
        m = rng.pick(by_id(r.metabolites))
        r.subtract_metabolites({m: r.metabolites[m]})
        return f"drop {m.id} from {r.id}"
    if kind == "bump_coeff":
        r = rng.pick(internal)
        m = rng.pick(by_id(r.metabolites))
        c = r.metabolites[m]
        r.add_metabolites({m: 1 if c > 0 else -1})
        return f"coefficient of {m.id} in {r.id}: {c:g} -> {r.metabolites[m]:g}"
    if kind == "shift_charge":
        m = rng.pick(mets)
        m.charge = (m.charge or 0) + 1
        return f"charge of {m.id} +1"
    if kind == "erase_formula":
        m = rng.pick(mets)
        m.formula = None
        return f"erase formula of {m.id}"
    if kind == "erase_charge":
        m = rng.pick(mets)
        m.charge = None
        return f"erase charge of {m.id}"
    if kind == "make_irreversible":
        r = rng.pick([r for r in by_id(model.reactions) if r.reversibility])
        r.lower_bound = 0
        return f"{r.id} irreversible"
    if kind == "delete_reaction":
        r = rng.pick([r for r in by_id(model.reactions) if not r.id.startswith("BIOMASS")])
        r.remove_from_model(remove_orphans=False)
        return f"delete {r.id}"
    if kind == "isolate_metabolite":
        m = rng.pick([m for m in mets if len(m.reactions) <= 3])
        rs = by_id(m.reactions)
        for r in rs:
            r.remove_from_model(remove_orphans=False)
        return f"isolate {m.id}: delete {', '.join(r.id for r in rs)}"
    if kind == "delete_exchange":
        r = rng.pick(by_id(model.exchanges))
        r.remove_from_model(remove_orphans=False)
        return f"delete {r.id}"
    if kind in ("delete_producers", "delete_consumers"):
        only = H.is_only_substrate if kind == "delete_producers" else H.is_only_product
        cands = [m for m in mets
                 if any(only(m, r) for r in m.reactions) and not any(r in model.exchanges for r in m.reactions)]
        m = rng.pick(cands)
        rs = [r for r in by_id(m.reactions) if not only(m, r) and not r.id.startswith("BIOMASS")]
        for r in rs:
            r.remove_from_model(remove_orphans=False)
        note = f"{kind.replace('_', ' ')} of {m.id}: {', '.join(r.id for r in rs) or 'none'}"
        if kind == "delete_producers":
            left = by_id(m.reactions)
            for r in left:
                write_backward(r)
            note += f"; write backward {', '.join(r.id for r in left)}"
        return note
    if kind == "write_backward":
        r = rng.pick([r for r in by_id(model.reactions) if not r.reversibility])
        write_backward(r)
        return f"write backward {r.id}"
    raise ValueError(kind)


KINDS = ["drop_participant", "bump_coeff", "shift_charge", "erase_formula",
         "erase_charge", "make_irreversible", "delete_reaction", "isolate_metabolite",
         "delete_exchange", "delete_producers", "delete_consumers", "write_backward"]


def reference(model):
    """memote's verdicts, computed by memote's own functions."""
    from memote.support import consistency as C
    from memote.support import consistency_helpers as H

    ids = lambda xs: sorted(x.id for x in xs)
    internal = H.get_internals(model)
    return {
        "internal": ids(internal),
        "mass_unbalanced": ids(C.find_mass_unbalanced_reactions(internal)),
        "charge_unbalanced": ids(C.find_charge_unbalanced_reactions(internal)),
        "orphan": ids(C.find_orphans(model)),
        "deadend": ids(C.find_deadends(model)),
        "disconnected": ids(C.find_disconnected(model)),
    }


def num(x):
    x = float(x)
    return str(int(x)) if x == int(x) else repr(x)


def emit(model, ref, name, notes):
    import cobra

    rid = lambda r: "R_" + r.id
    mid = lambda m: "M_" + m.id
    ext = cobra.medium.find_external_compartment(model)
    out = [
        f"# GENERATED by tools/memote_ref.py build — do not edit.",
        f"# BiGG {MODEL}, memote 0.17.0. Variant: {name}.",
    ]
    out += [f"# mutation: {n}" for n in notes]
    out += ["", "include rules.agl", "", f"fact ext: external(compartment: {ext}) @ [curated_db]"]
    elements = sorted({e for m in model.metabolites for e in m.elements})
    out += [f"fact el_{e}: element(id: {e}) @ [curated_db]" for e in elements]
    for m in sorted(model.metabolites, key=lambda m: m.id):
        k = m.id
        out += ["", f"# {m.id}: {m.name}", f"fact sp_{k}: species(id: {mid(m)}) @ [curated_db]",
                f"fact cp_{k}: compartment(species: {mid(m)}, id: {m.compartment}) @ [curated_db]"]
        if m.elements:
            out.append(f"fact fk_{k}: formula_known(species: {mid(m)}) @ [curated_db]")
            out += [f"fact co_{k}_{e}: composition(species: {mid(m)}, element: {e}, n: {num(n)}) @ [curated_db]"
                    for e, n in sorted(m.elements.items())]
        if m.charge is not None:
            out.append(f"fact ch_{k}: charge(species: {mid(m)}, value: {num(m.charge)}) @ [curated_db]")
    for r in sorted(model.reactions, key=lambda r: r.id):
        k = r.id
        out += ["", f"# {r.id}: {r.reaction}", f"fact rx_{k}: reaction(id: {rid(r)}) @ [curated_db]",
                f"fact bd_{k}: bounds(reaction: {rid(r)}, lower: {num(r.lower_bound)}, upper: {num(r.upper_bound)}) @ [curated_db]"]
        sbo = r.annotation.get("sbo")
        if sbo:
            out.append(f"fact sbo_{k}: sbo(reaction: {rid(r)}, term: {sbo.replace(':', '_')}) @ [curated_db]")
        for i, (m, c) in enumerate(sorted(r.metabolites.items(), key=lambda mc: mc[0].id)):
            side = "left" if c < 0 else "right"
            out.append(f"fact pa_{k}_{i}: participates(reaction: {rid(r)}, species: {mid(m)}, side: {side}, coeff: {num(abs(c))}) @ [curated_db]")
    out += ["", "# memote's verdicts."]
    internal = set(ref["internal"])
    for r in sorted(model.reactions, key=lambda r: r.id):
        yes = r.id in internal
        out.append(f"query requires_balance(reaction: {rid(r)}) @ expect {'yes' if yes else 'no'}")
        if yes:
            out.append(f"query mass_balanced(reaction: {rid(r)}) @ expect {'no' if r.id in ref['mass_unbalanced'] else 'yes'}")
            out.append(f"query charge_balanced(reaction: {rid(r)}) @ expect {'no' if r.id in ref['charge_unbalanced'] else 'yes'}")
    for m in sorted(model.metabolites, key=lambda m: m.id):
        for test in ("orphan", "deadend", "disconnected"):
            out.append(f"query {test}(species: {mid(m)}) @ expect {'yes' if m.id in ref[test] else 'no'}")
    (OUT / f"{name}.agl").write_text("\n".join(out) + "\n")


def build():
    import logging

    import cobra

    logging.disable(logging.WARNING)
    path = verified_model_path()
    OUT.mkdir(parents=True, exist_ok=True)
    summary = []
    for i in range(MUTANTS + 1):
        model = cobra.io.read_sbml_model(str(path))
        notes = []
        if i > 0:
            rng = SplitMix64(SEED + i)
            notes.append(mutate(model, KINDS[(i - 1) % len(KINDS)], rng))
            if i > len(KINDS):
                notes.append(mutate(model, rng.pick(KINDS), rng))
        name = MODEL if i == 0 else f"mutant-{i:02}"
        ref = reference(model)
        emit(model, ref, name, notes)
        found = {k: v for k, v in ref.items() if k != "internal" and v}
        summary.append(f"{name}: {'; '.join(notes) or 'original'} -> {found or 'clean'}")
    (OUT / "REFERENCE.txt").write_text("\n".join(summary) + "\n")
    print("\n".join(summary))


if __name__ == "__main__":
    {"fetch": fetch, "build": build}[sys.argv[1] if len(sys.argv) > 1 else "build"]()

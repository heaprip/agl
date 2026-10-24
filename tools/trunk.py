#!/usr/bin/env python3
"""Loader of the metabolism trunk from Rhea and ChEBI.

    tools/trunk.py fetch          download raw responses into data/raw/ and write MANIFEST
    tools/trunk.py fetch-classes  add ChEBI class ancestors (and those of conjugate
                                  acids) to data/raw/, keeping files already there
    tools/trunk.py build          build data/metabolism.agl and data/classes.agl
                                  from data/raw/, offline

Only `fetch` touches the network. `build` checks every raw file against
MANIFEST and is deterministic: two builds give the same bytes. The kernel
never reads the network; it reads the built file.

Standard library only.
"""

import hashlib
import json
import pathlib
import re
import sys
import urllib.parse
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
RAW = ROOT / "data" / "raw"
OUT = ROOT / "data" / "metabolism.agl"
CLASSES = ROOT / "data" / "classes.agl"

# The ten steps of glycolysis, found in Rhea by EC number (see docs/hypotheses.md, H34).
REACTIONS = [
    ("17825", "2.7.1.1", "hexokinase"),
    ("11816", "5.3.1.9", "glucose-6-phosphate isomerase"),
    ("16109", "2.7.1.11", "6-phosphofructokinase"),
    ("14729", "4.1.2.13", "fructose-bisphosphate aldolase"),
    ("18585", "5.3.1.1", "triose-phosphate isomerase"),
    ("10300", "1.2.1.12", "glyceraldehyde-3-phosphate dehydrogenase"),
    ("14801", "2.7.2.3", "phosphoglycerate kinase"),
    ("15901", "5.4.2.11", "phosphoglycerate mutase"),
    ("10164", "4.2.1.11", "enolase"),
    ("18157", "2.7.1.40", "pyruvate kinase"),
    # Beyond glycolysis: regenerating NAD(+) without oxygen.
    ("23444", "1.1.1.27", "L-lactate dehydrogenase"),
]

# Species needed by textbook reactions that are not in Rhea's reaction set.
EXTRA_SPECIES = ["15379"]  # dioxygen

RHEA_URL = "https://www.rhea-db.org/rhea/?query=RHEA:{id}&columns=rhea-id,equation,chebi-id&format=tsv"
OLS_TERM = "https://www.ebi.ac.uk/ols4/api/ontologies/chebi/terms?iri={iri}"
OLS_PARENTS = "https://www.ebi.ac.uk/ols4/api/ontologies/chebi/terms/{enc}/parents?size=100"
OLS_ANCESTORS = "https://www.ebi.ac.uk/ols4/api/ontologies/chebi/terms/{enc}/ancestors?size=1000"
OLS_ACIDS = "https://www.ebi.ac.uk/ols4/api/ontologies/chebi/terms/{enc}/is_deprotonated_form_of?size=100"


USER_AGENT = "agl-trunk-loader/0.1 (+https://github.com/heaprip/agl)"


def get(url):
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read()


def chebi_iri(cid):
    return f"http://purl.obolibrary.org/obo/CHEBI_{cid}"


def rhea_participants(tsv):
    """(equation, [chebi ids]) from a one-reaction Rhea TSV."""
    lines = [l for l in tsv.decode().splitlines() if l.strip()]
    if len(lines) != 2:
        raise SystemExit(f"unexpected Rhea response: {lines!r}")
    _, equation, ids = lines[1].split("\t")
    return equation, [i.removeprefix("CHEBI:") for i in ids.split(";")]


def fetch():
    (RAW / "rhea").mkdir(parents=True, exist_ok=True)
    (RAW / "chebi").mkdir(parents=True, exist_ok=True)
    species = set()
    for rid, _, _ in REACTIONS:
        body = get(RHEA_URL.format(id=rid))
        (RAW / "rhea" / f"RHEA_{rid}.tsv").write_bytes(body)
        species.update(rhea_participants(body)[1])
    species.update(EXTRA_SPECIES)
    for cid in sorted(species, key=int):
        iri = chebi_iri(cid)
        term = get(OLS_TERM.format(iri=urllib.parse.quote(iri, safe="")))
        (RAW / "chebi" / f"CHEBI_{cid}.term.json").write_bytes(term)
        enc = urllib.parse.quote(urllib.parse.quote(iri, safe=""), safe="")
        parents = get(OLS_PARENTS.format(enc=enc))
        (RAW / "chebi" / f"CHEBI_{cid}.parents.json").write_bytes(parents)
    files = write_manifest()
    print(f"fetched {len(REACTIONS)} reactions, {len(species)} species, {len(files)} files")


def write_manifest():
    files = sorted(p for p in RAW.rglob("*") if p.is_file() and p.name != "MANIFEST")
    manifest = "".join(f"{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(RAW)}\n" for p in files)
    (RAW / "MANIFEST").write_text(manifest)
    return files


def enc_iri(cid):
    return urllib.parse.quote(urllib.parse.quote(chebi_iri(cid), safe=""), safe="")


def fetch_once(path, url):
    """Download into path unless it is already there: earlier raw files stay as they were."""
    if not path.exists():
        path.write_bytes(get(url))
    return path.read_bytes()


def terms(body):
    return json.loads(body).get("_embedded", {}).get("terms", [])


def inchi_core(term):
    """InChI without the protonation layer: a charged form and its acid share it."""
    inchi = (term.get("annotation", {}).get("inchi_string") or [None])[0]
    if inchi is None:
        return None
    return "/".join(l for l in inchi.split("/") if not l.startswith("p"))


def charge(term):
    return (term.get("annotation", {}).get("charge") or [0.0])[0]


def species_ids():
    ids = set(EXTRA_SPECIES)
    for rid, _, _ in REACTIONS:
        ids.update(rhea_participants((RAW / "rhea" / f"RHEA_{rid}.tsv").read_bytes())[1])
    return sorted(ids, key=int)


def conjugate_acids(cid):
    """Acids whose deprotonation gives this species, by the relation in ChEBI.

    OLS returns the relation mixed with roles, functional parents and even
    conjugate bases, so an acid is kept only if its InChI without the
    protonation layer is the species' own and its charge is higher."""
    own = terms((RAW / "chebi" / f"CHEBI_{cid}.term.json").read_bytes())[0]
    acids = []
    for t in terms((RAW / "chebi" / f"CHEBI_{cid}.acids.json").read_bytes()):
        aid = t["obo_id"].removeprefix("CHEBI:")
        term = terms((RAW / "chebi" / f"CHEBI_{aid}.term.json").read_bytes())[0]
        same = inchi_core(term) is not None and inchi_core(term) == inchi_core(own)
        if same and charge(term) > charge(own):
            acids.append(aid)
    return sorted(acids, key=int)


def fetch_classes():
    for cid in species_ids():
        body = fetch_once(RAW / "chebi" / f"CHEBI_{cid}.acids.json", OLS_ACIDS.format(enc=enc_iri(cid)))
        for t in terms(body):
            aid = t["obo_id"].removeprefix("CHEBI:")
            fetch_once(RAW / "chebi" / f"CHEBI_{aid}.term.json",
                       OLS_TERM.format(iri=urllib.parse.quote(chebi_iri(aid), safe="")))
        for x in [cid] + conjugate_acids(cid):
            fetch_once(RAW / "chebi" / f"CHEBI_{x}.ancestors.json", OLS_ANCESTORS.format(enc=enc_iri(x)))
    files = write_manifest()
    print(f"classes fetched; {len(files)} raw files")


def verified_raw():
    manifest = (RAW / "MANIFEST").read_text()
    for line in manifest.splitlines():
        digest, rel = line.split("  ", 1)
        if hashlib.sha256((RAW / rel).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"{rel}: content does not match MANIFEST")
    return hashlib.sha256(manifest.encode()).hexdigest()


def parse_formula(f):
    """Element counts of a formula such as C10H12N5O13P3; None if not a plain formula."""
    if not re.fullmatch(r"([A-Z][a-z]?\d*)+", f):
        return None
    counts = {}
    for el, n in re.findall(r"([A-Z][a-z]?)(\d*)", f):
        counts[el] = counts.get(el, 0) + int(n or 1)
    return counts


def sides(equation, ids):
    """[(side, coeff, chebi id)] in equation order; Rhea lists ids in that order."""
    left, right = equation.split(" = ")
    out = []
    names = [("left", t) for t in left.split(" + ")] + [("right", t) for t in right.split(" + ")]
    if len(names) != len(ids):
        raise SystemExit(f"cannot align participants of `{equation}` with {ids}")
    for (side, term), cid in zip(names, ids):
        m = re.match(r"(\d+) (.*)", term)
        coeff = int(m.group(1)) if m else 1
        out.append((side, coeff, cid))
    return out


def build():
    manifest_hash = verified_raw()
    lines = [
        "# GENERATED by tools/trunk.py build — do not edit.",
        f"# Sources: Rhea (reactions), ChEBI via OLS (formulas, charges, is_a). MANIFEST sha256 {manifest_hash}",
        "",
        "status measurement > curated_db > textbook > llm_proposal",
        "relation participates(reaction, species, side, coeff)",
        "relation composition(species, element, n)",
        "unique composition(n) by (species, element)",
        "",
    ]
    species = {}
    for rid, ec, name in REACTIONS:
        equation, ids = rhea_participants((RAW / "rhea" / f"RHEA_{rid}.tsv").read_bytes())
        lines.append(f"# RHEA:{rid} EC {ec} {name}: {equation}")
        lines.append(f"fact rx_{rid}: reaction(id: RHEA_{rid}) @ [curated_db]")
        for k, (side, coeff, cid) in enumerate(sides(equation, ids)):
            species[cid] = None
            lines.append(
                f"fact pa_{rid}_{k}: participates(reaction: RHEA_{rid}, species: CHEBI_{cid}, side: {side}, coeff: {coeff}) @ [curated_db]"
            )
        lines.append("")
    for cid in EXTRA_SPECIES:
        species[cid] = None
    in_set = set(species)
    for cid in sorted(species, key=int):
        term = json.loads((RAW / "chebi" / f"CHEBI_{cid}.term.json").read_bytes())["_embedded"]["terms"][0]
        ann = term.get("annotation", {})
        formula = (ann.get("generalized_empirical_formula") or [None])[0]
        charge = (ann.get("charge") or [None])[0]
        lines.append(f"# CHEBI:{cid} {term['label']}: {formula}, charge {charge}")
        counts = parse_formula(formula) if formula else None
        if counts is None or charge is None:
            lines.append(f"# no plain formula or charge: composition left unknown")
        else:
            for el in sorted(counts):
                lines.append(f"fact co_{cid}_{el}: composition(species: CHEBI_{cid}, element: {el}, n: {counts[el]}) @ [curated_db]")
            lines.append(f"fact co_{cid}_charge: composition(species: CHEBI_{cid}, element: charge, n: {int(charge)}) @ [curated_db]")
            lines.append(f"fact fk_{cid}: formula_known(species: CHEBI_{cid}) @ [curated_db]")
        parents = json.loads((RAW / "chebi" / f"CHEBI_{cid}.parents.json").read_bytes())
        for p in sorted(t["obo_id"].removeprefix("CHEBI:") for t in parents.get("_embedded", {}).get("terms", [])):
            if p in in_set:
                lines.append(f"fact isa_{cid}_{p}: is_a(species: CHEBI_{cid}, parent: CHEBI_{p}) @ [curated_db]")
        lines.append("")
    # Top classes within the set: species with no parent inside it. Computed
    # from the ChEBI hierarchy restricted to the set, so it is data, not a guess.
    has_parent = set()
    for cid in species:
        parents = json.loads((RAW / "chebi" / f"CHEBI_{cid}.parents.json").read_bytes())
        if any(t["obo_id"].removeprefix("CHEBI:") in in_set for t in parents.get("_embedded", {}).get("terms", [])):
            has_parent.add(cid)
    for cid in sorted(in_set - has_parent, key=int):
        lines.append(f"fact top_{cid}: top(species: CHEBI_{cid}) @ [curated_db]")
    OUT.write_text("\n".join(lines) + "\n")
    print(f"built {OUT.relative_to(ROOT)}: {len(REACTIONS)} reactions, {len(species)} species")
    if (RAW / "chebi" / f"CHEBI_{species_ids()[0]}.acids.json").exists():
        build_classes(manifest_hash)


def build_classes(manifest_hash):
    """data/classes.agl: every ChEBI class of a species, of its conjugate acids and the acids themselves.

    Rhea names charged forms (glycerone phosphate(2-)); ChEBI hangs the
    chemical classes (ketose phosphate) on the neutral acid. A class is a
    fact `class_of`; its label is kept as a `# class` comment for reports."""
    lines = [
        "# GENERATED by tools/trunk.py build — do not edit.",
        f"# Sources: ChEBI via OLS (is_a ancestors of species and of their conjugate acids). MANIFEST sha256 {manifest_hash}",
        "",
        "relation class_of(species, class)",
        "",
    ]
    labels = {}
    for cid in species_ids():
        if not (RAW / "chebi" / f"CHEBI_{cid}.acids.json").exists():
            raise SystemExit("classes are not fetched: run tools/trunk.py fetch-classes")
        acids = conjugate_acids(cid)
        classes = set(acids)
        for x in [cid] + acids:
            for t in terms((RAW / "chebi" / f"CHEBI_{x}.ancestors.json").read_bytes()):
                classes.add(t["obo_id"].removeprefix("CHEBI:"))
        for a in acids:
            labels[a] = terms((RAW / "chebi" / f"CHEBI_{a}.term.json").read_bytes())[0]["label"]
        for x in [cid] + acids:
            for t in terms((RAW / "chebi" / f"CHEBI_{x}.ancestors.json").read_bytes()):
                labels[t["obo_id"].removeprefix("CHEBI:")] = t["label"]
        acid_note = ", ".join(f"CHEBI:{a}" for a in acids) or "none"
        lines.append(f"# CHEBI:{cid}: {len(classes)} classes; conjugate acids: {acid_note}")
        for k in sorted(classes, key=int):
            lines.append(f"fact cl_{cid}_{k}: class_of(species: CHEBI_{cid}, class: CHEBI_{k}) @ [curated_db]")
        lines.append("")
    for k in sorted(labels, key=int):
        lines.append(f"# class CHEBI_{k}: {labels[k]}")
    CLASSES.write_text("\n".join(lines) + "\n")
    print(f"built {CLASSES.relative_to(ROOT)}: {len(labels)} classes")


if __name__ == "__main__":
    {"fetch": fetch, "fetch-classes": fetch_classes, "build": build}[sys.argv[1] if len(sys.argv) > 1 else ""]()

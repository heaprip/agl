//! Every case under `cases/` parses, lints clean and meets its expectations.

use std::collections::BTreeSet;
use std::fs;

const SI: &str = include_str!("../cases/lib/si.agl");

#[test]
fn cases_meet_expectations() {
    let mut paths: Vec<_> = fs::read_dir("cases")
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    assert!(!paths.is_empty());
    for path in paths
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "agl"))
    {
        let prog =
            agl::parse::parse_file(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let report = agl::run(&prog);
        assert!(
            !report.has_errors(),
            "{}: {:?}",
            path.display(),
            report.diags
        );
        let failed: Vec<_> = report
            .failed_queries()
            .map(|q| format!("line {}: {} -> {}", q.query.line, q.query.atom, q.verdict))
            .collect();
        assert!(failed.is_empty(), "{}: {failed:#?}", path.display());
    }
}

#[test]
fn is_ought_is_rejected() {
    let src = "
axis view
value view v1
normative_axis view
normative ought
axis world
value world w
fact f: child(person: x) @ world:w
rule bad defeasible @ world:w: ought(act: spare, person: ?p) <- child(person: ?p)
rule good defeasible @ world:w + view:v1: ought(act: spare, person: ?p) <- child(person: ?p)
";
    let report = agl::run(&agl::parse(src).unwrap());
    let codes: Vec<_> = report
        .diags
        .iter()
        .map(|d| (d.code, d.msg.contains("`bad`")))
        .collect();
    assert_eq!(codes, vec![("is-ought", true)]);
}

#[test]
fn unknown_role_is_reported() {
    let src = "
relation member_of(individual, taxon)
fact f: member_of(person: newton, taxon: homo_sapiens) @
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(report.diags.iter().any(|d| d.code == "unknown-role"));
}

#[test]
fn unknown_metaedge_occurrence_is_reported() {
    let src = "
fact target: object(name: sample) @
metaedge broken: &missing(subject: &target) @
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(
        report
            .diags
            .iter()
            .any(|diag| diag.code == "unknown-occurrence")
    );
}

#[test]
fn malformed_derived_metaedges_are_rejected_before_evaluation() {
    let src = "
fact relation_occ: relation_object(name: observes) @
fact seed_occ: seed(name: sample) @
rule symbol strict @: metaedge(relation: observes, subject: &seed_occ) <- seed(name: sample)
rule owns_id strict @: metaedge(occurrence: &seed_occ, relation: &relation_occ) <- seed(name: sample)
rule no_relation strict @: metaedge(subject: &seed_occ) <- seed(name: sample)
rule duplicate strict @: metaedge(relation: &relation_occ, subject: &seed_occ, subject: &relation_occ) <- seed(name: sample)
";
    let report = agl::run(&agl::parse(src).unwrap());
    let codes: BTreeSet<_> = report.diags.iter().map(|diag| diag.code).collect();
    assert!(codes.contains("bad-metaedge-endpoint"));
    assert!(codes.contains("reserved-metaedge-role"));
    assert!(codes.contains("bad-metaedge-head"));
    assert!(codes.contains("duplicate-metaedge-role"));
}

#[test]
fn overlapping_planes_conflict_disjoint_do_not() {
    let base = "
axis pressure
value pressure p1atm
value pressure hyperbaric
fact g: gas(name: n2) @
rule n1 defeasible @ pressure:p1atm: inert(gas: ?g) <- gas(name: ?g)
rule n2 defeasible @ pressure:hyperbaric: ¬inert(gas: ?g) <- gas(name: ?g)
";
    let disjoint = agl::run(&agl::parse(base).unwrap());
    assert!(disjoint.conflicts.is_empty());
    let overlapping =
        agl::run(&agl::parse(&format!("{base}overlap pressure p1atm hyperbaric\n")).unwrap());
    assert_eq!(overlapping.conflicts.len(), 1);
    assert_eq!(overlapping.conflicts[0].conflict.positive, "inert(gas: n2)");
}

#[test]
fn dimension_mismatch_is_an_error() {
    let src = "
fact g: dG(value: -16.7[kJ/mol]) @
fact t: temperature(value: 310[K]) @
rule bad strict @: hot(x: ?g) <- dG(value: ?g), temperature(value: ?t), ?g < ?t
";
    let report = agl::run(&agl::parse(&format!("{SI}{src}")).unwrap());
    assert!(report.has_errors());
    assert!(
        report
            .errors
            .iter()
            .any(|e| e.contains("rule `bad`") && e.contains("comparing")),
        "{:?}",
        report.errors
    );
}

#[test]
fn hobbes_collapse_is_a_uniqueness_conflict_only_in_the_absolute_view() {
    let src = std::fs::read_to_string("cases/theseus.agl").unwrap();
    let report = agl::run(&agl::parse(&src).unwrap());
    let found: Vec<_> = report
        .conflicts
        .iter()
        .map(|c| {
            (
                format!("{:?}", c.conflict.kind),
                agl::model::plane_to_string(&c.context),
            )
        })
        .collect();
    assert_eq!(
        found,
        vec![("Uniqueness".to_string(), "{view:absolute}".to_string())]
    );
}

#[test]
fn units_convert_to_si() {
    let src = "
fact a: p(value: 760[mmHg]) @
fact b: q(value: 1[atm]) @
rule c strict @: close(x: 1) <- p(value: ?a), q(value: ?b), ((?a - ?b) / ?b)^2 < 0.0001
query close(x: 1) @ expect yes
";
    let report = agl::run(&agl::parse(&format!("{SI}{src}")).unwrap());
    assert!(!report.has_errors(), "{:?}", report.errors);
    assert!(report.failed_queries().next().is_none());
}

/// Decision 23: the kernel knows no units of its own.
#[test]
fn units_come_only_from_declarations() {
    let err = agl::parse("fact a: p(value: 1[m]) @\n").unwrap_err();
    assert!(err.contains("unknown unit `m`"), "{err}");
    // Any base quantity will do, and a unit may be defined through a later one.
    let src = "
unit lap = 4 stride
quantity pace stride
fact a: p(value: 2[lap]) @
fact b: q(value: 8[stride]) @
rule c strict @: same(x: 1) <- p(value: ?a), q(value: ?b), ?a = ?b
query same(x: 1) @ expect yes
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(!report.has_errors(), "{:?}", report.errors);
    assert!(report.failed_queries().next().is_none());
}

#[test]
fn scan_sees_a_meet_of_three_planes() {
    let src = "
axis x
value x a
axis y
value y b
axis z
value z c
fact f1: p(i: k) @ x:a
rule rq defeasible @ y:b: q(i: ?i) <- p(i: ?i)
rule rnq defeasible @ z:c: ¬q(i: ?i) <- p(i: ?i)
";
    let report = agl::run(&agl::parse(src).unwrap());
    let found: Vec<String> = report
        .conflicts
        .iter()
        .map(|c| {
            format!(
                "{} {}",
                c.conflict.positive,
                agl::model::plane_to_string(&c.context)
            )
        })
        .collect();
    assert_eq!(found, ["q(i: k) {x:a, y:b, z:c}"]);
}

#[test]
fn a_plane_that_undermines_its_situation_is_a_conflict() {
    // In the root, `k` is situated in w:x; in w:x a narrower rule denies it.
    let src = "
axis w
value w x
fact b: base(id: k) @
rule s1 defeasible @: situated(context: k, axis: w, value: x) <- base(id: k)
rule s2 defeasible @ w:x: ¬situated(context: k, axis: w, value: x) <- base(id: k)
rule g defeasible @ w:x: good(id: k) <- base(id: k)
query good(id: k) @ situate k expect conflict
";
    let report = agl::run(&agl::parse(src).unwrap());
    let q = &report.queries[0];
    assert_eq!(q.verdict, agl::model::Verdict::Conflict);
    assert!(
        q.explanation.contains("undermines its own plane"),
        "{}",
        q.explanation
    );
}

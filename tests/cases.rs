//! Every case under `cases/` parses, lints clean and meets its expectations.

use std::fs;

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
        let src = fs::read_to_string(path).unwrap();
        let prog = agl::parse(&src).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
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

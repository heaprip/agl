//! Reflection R1: diagnosis of failed expectations and conflicts.

use agl::reflect::{Kind, diagnose};

const SAME_PLANE: &str = "
axis taxon
value taxon Insecta
value taxon Mammalia
plane insects = taxon:Insecta
plane mammals = taxon:Mammalia
fact i1: insect(organism: locust) @ insects
fact i2: insect(organism: midge_larva) @ insects
fact i3: has_hemoglobin(organism: midge_larva) @ insects
rule r_ins defeasible @ insects: ¬transports_o2(organism: ?x) <- insect(organism: ?x)
rule ex1 defeasible @ insects: transports_o2(organism: ?x) <- insect(organism: ?x), has_hemoglobin(organism: ?x)
query transports_o2(organism: locust) @ insects expect no
query transports_o2(organism: midge_larva) @ insects expect yes
";

#[test]
fn an_exception_in_the_same_plane_cannot_be_fixed_by_removal() {
    let ds = diagnose(&agl::parse(SAME_PLANE).unwrap());
    let wrong = ds
        .iter()
        .find(|d| d.kind == Kind::WrongAnswer)
        .expect("the midge expectation fails");
    assert!(
        wrong
            .target
            .starts_with("transports_o2(organism: midge_larva)")
    );
    // Removing either rule breaks the locust or the midge: structure is needed, not deletion.
    assert!(wrong.culprits.is_empty(), "{:?}", wrong.culprits);
    let conflict = ds
        .iter()
        .find(|d| d.kind == Kind::Conflict)
        .expect("the conflict is reported");
    assert!(
        conflict.notes.iter().any(|n| n.contains("share one plane")),
        "{:?}",
        conflict.notes
    );
    // Removing ex1 settles the conflict but answers the midge `no` against the
    // expectation `yes`: the teacher counts even where it already fails.
    assert!(conflict.culprits.is_empty(), "{:?}", conflict.culprits);
}

#[test]
fn a_rule_in_a_disjoint_plane_is_named_as_the_reason_for_silence() {
    let src =
        format!("{SAME_PLANE}query transports_o2(organism: midge_larva) @ mammals expect yes\n");
    let ds = diagnose(&agl::parse(&src).unwrap());
    let missing = ds
        .iter()
        .find(|d| d.kind == Kind::Missing)
        .expect("the mammal expectation is missing");
    assert!(
        missing
            .notes
            .iter()
            .any(|n| n.contains("`ex1`") && n.contains("disjoint from the context")),
        "{:?}",
        missing.notes
    );
}

#[test]
fn current_cases_diagnose_only_the_hobbes_collapse_and_keep_it() {
    let mut found = Vec::new();
    let mut paths: Vec<_> = std::fs::read_dir("cases")
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    paths.sort();
    for path in paths
        .iter()
        .filter(|p| p.extension().is_some_and(|e| e == "agl"))
    {
        let prog = agl::parse(&std::fs::read_to_string(path).unwrap()).unwrap();
        for d in diagnose(&prog) {
            let kept = d.notes.iter().any(|n| {
                n.contains("without [collapse] it settles, but expectations on lines 68, 69 fail")
            });
            found.push((
                path.file_name().unwrap().to_string_lossy().to_string(),
                d.kind,
                d.culprits,
                kept,
            ));
        }
    }
    // Hobbes' absurdity is wanted in this case: the expectations on lines 68 and 69
    // ask for the collapse, so no removal is offered and the note says why.
    // Kinship has seven conflicts, all wanted too: several mothers where the
    // genetic, gestational and legal planes meet. Nothing is offered to remove.
    let mut want = vec![("kinship.agl".to_string(), Kind::Conflict, vec![], false); 7];
    want.push(("theseus.agl".to_string(), Kind::Conflict, vec![], true));
    assert_eq!(found, want);
}

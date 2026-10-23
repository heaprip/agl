//! Learning by theoretical generalization: the template `subset` over the
//! known vocabulary, fitted on training examples, judged on held-out ones.

#[test]
fn viability_is_learned_and_holds_on_held_out_examples() {
    let prog = agl::parse_file(std::path::Path::new("cases/learning/viability.agl")).unwrap();
    let (hs, notes) = agl::learn::learn(&prog, "viable");
    assert_eq!(hs.len(), 1, "{notes:?}");
    assert_eq!(
        hs[0].reading,
        "viable(system: s) ⇐ every x with consumed(system: s, species: x) has available(species: x)"
    );
    assert_eq!(hs[0].train, (3, 3));
    assert_eq!(hs[0].heldout, (6, 6));
}

#[test]
fn one_positive_example_underdetermines_and_held_out_decides() {
    let mut prog = agl::parse_file(std::path::Path::new("cases/learning/viability.agl")).unwrap();
    // Keep only the positive anaerobic example for training.
    prog.queries
        .retain(|q| q.heldout || q.atom.to_string() == "viable(system: fermenting)");
    let (hs, notes) = agl::learn::learn(&prog, "viable");
    assert!(
        notes[0].contains("20 account for every training example"),
        "{notes:?}"
    );
    assert!(hs[0].reading.contains("has available(species: x)"));
    assert_eq!(hs[0].heldout, (6, 6));
    assert!(hs[1..].iter().all(|h| h.heldout.0 < 6));
}

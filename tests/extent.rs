//! Where a statement holds and what goes with what across planes (H52).

use agl::extent::{Holds, extents, implications, render_extents, render_implications};
use agl::model::plane_to_string;
use agl::sim::permute;

fn kinship() -> agl::model::Program {
    agl::parse(&std::fs::read_to_string("cases/kinship.agl").unwrap()).unwrap()
}

#[test]
fn mother_by_birth_holds_where_gestation_is_seen() {
    let prog = kinship();
    let pat = agl::parse::parse_atom("mother(ego: mira, alter: vera)").unwrap();
    let (exts, complete) = extents(&prog, &pat);
    assert!(complete);
    assert_eq!(exts.len(), 1);
    let yes: Vec<String> = exts[0]
        .by_context
        .iter()
        .filter(|(_, h)| *h == Holds::Yes)
        .map(|(p, _)| plane_to_string(p))
        .collect();
    assert!(!yes.is_empty());
    assert!(yes.iter().all(|p| p.contains("gestation")), "{yes:?}");
}

/// Declared before the first run: "mother → parent" fails only in planes that
/// see gestation, and only on the mothers by birth.
#[test]
fn mother_implies_parent_except_by_gestation() {
    let imp = implications(&kinship());
    let i = imp
        .near
        .iter()
        .find(|i| i.premise[0] == "mother" && i.conclusion[0] == "parent")
        .expect("mother → parent is a near implication");
    assert!(
        i.exceptions
            .iter()
            .all(|(ctx, _)| ctx.contains("gestation"))
    );
    let who: std::collections::BTreeSet<&str> =
        i.exceptions.iter().map(|(_, o)| o.as_str()).collect();
    assert_eq!(
        who.into_iter().collect::<Vec<_>>(),
        ["alter: tamara, ego: lev", "alter: vera, ego: mira"]
    );
    assert!(
        imp.exact
            .iter()
            .any(|i| i.premise[0] == "father" && i.conclusion[0] == "parent")
    );
}

#[test]
fn extents_and_implications_do_not_depend_on_statement_order() {
    let prog = kinship();
    let pat = agl::parse::parse_atom("mother(ego: ?e, alter: ?a)").unwrap();
    let show = |p: &agl::model::Program| {
        let (e, c) = extents(p, &pat);
        (render_extents(&e, c), render_implications(&implications(p)))
    };
    let base = show(&prog);
    for seed in 0..3 {
        assert_eq!(base, show(&permute(&prog, seed)), "permutation {seed}");
    }
}

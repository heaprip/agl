//! Contract tests for the shared identity/intension/extent/evidence carrier.
//! These exercise the real rule evaluator and relation bank, not a parallel
//! prototype store.

use std::collections::BTreeSet;

use agl::bank::{Bank, Ext};
use agl::eval::evaluate;
use agl::meta::{ClaimId, Evidence, EvidenceState, Intension, Metagraph};
use agl::model::{Name, Plane, Strength};

fn occurrence_ids(src: &str) -> BTreeSet<String> {
    let out = evaluate(&agl::parse(src).unwrap(), &Plane::new());
    out.db
        .projections()
        .into_iter()
        .map(|p| p.entity.to_string())
        .collect()
}

#[test]
fn evaluator_keeps_occurrences_but_shares_the_claim() {
    let src = "
relation p(x)
relation q(x)
fact left: p(x: a) @
fact right: p(x: a) @
rule lift strict @: q(x: ?x) <- p(x: ?x)
";
    let out = evaluate(&agl::parse(src).unwrap(), &Plane::new());
    let (_, p) = out.db.values().find(|(atom, _)| atom.rel == "p").unwrap();
    let (_, q) = out.db.values().find(|(atom, _)| atom.rel == "q").unwrap();

    assert_eq!(p.len(), 2, "both asserted relation occurrences survive");
    assert_ne!(p[0].entity.id, p[1].entity.id);
    assert_ne!(p[0].evidence.id, p[1].evidence.id);
    assert_eq!(p[0].evidence.conclusion, p[1].evidence.conclusion);

    // A claim is an OR-node. The rule depends on that claim, rather than
    // multiplying once for every alternative proof of it.
    assert_eq!(q.len(), 1);
    assert_eq!(
        q[0].evidence.premises,
        vec![p[0].evidence.conclusion.clone()]
    );

    let projections: Vec<_> = out
        .db
        .projections()
        .into_iter()
        .filter(|x| x.extent.rel == "p")
        .collect();
    assert_eq!(projections.len(), 2);
    assert_eq!(projections[0].claim, projections[1].claim);
    assert_eq!(projections[0].extent, projections[1].extent);
    assert_ne!(projections[0].entity, projections[1].entity);
}

#[test]
fn evaluator_ids_do_not_depend_on_source_order() {
    let first = "
fact left: p(x: a) @
fact right: p(x: a) @
rule lift strict @: q(x: ?x) <- p(x: ?x)
";
    let second = "
fact right: p(x: a) @
fact left: p(x: a) @
rule lift strict @: q(x: ?x) <- p(x: ?x)
";
    assert_eq!(occurrence_ids(first), occurrence_ids(second));
}

#[test]
fn retracting_one_alternative_keeps_the_claim_supported() {
    let src = "
fact left: p(x: a) @
fact right: p(x: a) @
rule lift strict @: q(x: ?x) <- p(x: ?x)
";
    let out = evaluate(&agl::parse(src).unwrap(), &Plane::new());
    let mut graph = Metagraph::new();
    for (_, derivations) in out.db.values() {
        for derivation in derivations {
            graph.add_evidence(derivation.evidence.clone()).unwrap();
        }
    }
    for (_, derivations) in out.db.values() {
        for derivation in derivations {
            graph.add_entity(derivation.entity.clone()).unwrap();
        }
    }
    for projection in out.db.projections() {
        graph.add_projection(projection).unwrap();
    }

    let left = graph
        .evidence()
        .find(|evidence| evidence.operation == "left")
        .unwrap()
        .id
        .clone();
    let lift = graph
        .evidence()
        .find(|evidence| evidence.operation == "lift")
        .unwrap()
        .id
        .clone();
    let refuter = Evidence::new(
        ClaimId::named("event", "refute-left"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(left.clone(), refuter.id).unwrap();

    assert_eq!(graph.evidence_state(&left), Some(EvidenceState::Retracted));
    assert_eq!(graph.evidence_state(&lift), Some(EvidenceState::Active));
}

#[test]
fn bank_entity_and_claim_survive_context_change() {
    let extent = Ext::from_pairs(2, &[(0, 0), (0, 1), (1, 1)]);
    let root = Bank::grow_in(Name::from("r"), extent.clone(), Plane::new(), true);
    let situated = Bank::grow_in(
        Name::from("r"),
        extent,
        Plane::from([("frame".into(), "moving".into())]),
        true,
    );
    assert_eq!(root.entries.len(), situated.entries.len());
    for (a, b) in root.entries.iter().zip(&situated.entries) {
        assert_eq!(a.shape, b.shape);
        assert_eq!(a.entity.id, b.entity.id);
        assert_eq!(a.construction, b.construction);
        assert_eq!(a.projection.claim, b.projection.claim);
        assert_eq!(a.projection.extent, b.projection.extent);
        assert_ne!(a.evidence.id, b.evidence.id);
        assert_ne!(a.projection.context, b.projection.context);
    }
}

#[test]
fn bank_glue_is_the_shared_intension_not_only_an_index_plan() {
    let extent = Ext::from_pairs(2, &[(0, 1), (1, 0)]);
    let bank = Bank::grow(Name::from("r"), extent, true);
    let glued = bank
        .entries
        .iter()
        .find(|entry| matches!(entry.entity.intension, Intension::Glue { .. }));
    let glued = glued.expect("bank must expose a glued entity");
    let Intension::Glue {
        parts,
        wiring: _,
        interface: _,
        operation: _,
    } = &glued.entity.intension
    else {
        unreachable!()
    };
    assert!(!parts.is_empty());
    assert_eq!(glued.projection.entity, glued.entity.id);
    assert_eq!(glued.projection.evidence, glued.evidence.id);
}

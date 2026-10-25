//! Architectural killer: occurrence identity is not a contextual extent.
//! Every construction and projection comes from the production relation bank.

use agl::bank::{Bank, ExactRelation, Ext};
use agl::journal::Journal;
use agl::meta::{
    ClaimId, EntityId, Evidence, EvidenceState, Intension, Metaedge, Metagraph, Part, PortBinding,
    Projection,
};
use agl::model::{Name, Plane, Strength};

fn plane(value: &str) -> Plane {
    Plane::from([("world".into(), value.into())])
}

fn ingest(graph: &mut Metagraph<Ext>, bank: &Bank) {
    for entry in &bank.entries {
        graph.add_evidence(entry.construction.clone()).unwrap();
        graph.add_evidence(entry.evidence.clone()).unwrap();
        graph.add_entity(entry.entity.clone()).unwrap();
        graph.add_projection(entry.projection.clone()).unwrap();
    }
}

fn exact_graph(bank: &Bank, sparse: bool) -> Metagraph<ExactRelation> {
    let mut graph = Metagraph::new();
    for entry in &bank.entries {
        graph.add_evidence(entry.construction.clone()).unwrap();
        graph.add_evidence(entry.evidence.clone()).unwrap();
        graph.add_entity(entry.entity.clone()).unwrap();
        let extent = if sparse {
            ExactRelation::sparse(
                entry.projection.extent.n(),
                &entry.projection.extent.pairs(),
            )
            .unwrap()
        } else {
            ExactRelation::dense(entry.projection.extent.clone())
        };
        graph
            .add_projection(Projection {
                claim: entry.projection.claim.clone(),
                entity: entry.projection.entity.clone(),
                context: entry.projection.context.clone(),
                extent,
                evidence: entry.projection.evidence.clone(),
            })
            .unwrap();
    }
    graph
}

/// Two bank constructions which the small world cannot distinguish but the
/// larger world can. Both must be genuine glue nodes, not named fixtures.
fn witnesses<'a>(small: &'a Bank, large: &'a Bank) -> (&'a agl::bank::Entry, &'a agl::bank::Entry) {
    for (i, a) in small.entries.iter().enumerate() {
        if !matches!(a.entity.intension, Intension::Glue { .. }) {
            continue;
        }
        for b in &small.entries[i + 1..] {
            if !matches!(b.entity.intension, Intension::Glue { .. })
                || a.projection.extent != b.projection.extent
            {
                continue;
            }
            let Some(a_large) = large
                .entries
                .iter()
                .find(|entry| entry.entity.id == a.entity.id)
            else {
                continue;
            };
            let Some(b_large) = large
                .entries
                .iter()
                .find(|entry| entry.entity.id == b.entity.id)
            else {
                continue;
            };
            if a_large.projection.extent != b_large.projection.extent {
                return (a, b);
            }
        }
    }
    panic!("the real bank produced no identity/extent witnesses")
}

fn add_equality<T: Clone + PartialEq>(
    graph: &mut Metagraph<T>,
    left: &agl::bank::Entry,
    right: &agl::bank::Entry,
    context: Plane,
) -> Evidence {
    let evidence = Evidence::new(
        ClaimId::derived(
            "equal-at",
            [left.entity.id.as_str(), right.entity.id.as_str()],
        ),
        "compare-extents",
        vec![
            left.projection.claim.clone(),
            right.projection.claim.clone(),
        ],
        Strength::Strict,
        context.clone(),
    );
    graph.add_evidence(evidence.clone()).unwrap();
    graph
        .add_equal_at(
            left.entity.id.clone(),
            right.entity.id.clone(),
            context,
            evidence.id.clone(),
        )
        .unwrap();
    evidence
}

fn add_link<T: Clone + PartialEq>(
    graph: &mut Metagraph<T>,
    relation: &agl::bank::Entry,
    target: &agl::bank::Entry,
    context: Plane,
    role: &str,
) -> EntityId {
    let evidence = Evidence::new(
        ClaimId::derived("linked", [role, target.entity.id.as_str()]),
        "link-relation",
        vec![
            relation.construction.conclusion.clone(),
            target.construction.conclusion.clone(),
            target.projection.claim.clone(),
        ],
        Strength::Strict,
        context.clone(),
    );
    graph.add_evidence(evidence.clone()).unwrap();
    let edge = Metaedge::new(
        relation.entity.id.clone(),
        vec![PortBinding::new(role, target.entity.id.clone())],
        context,
        &evidence,
    );
    let id = edge.entity.id.clone();
    graph.add_metaedge(edge).unwrap();
    id
}

#[test]
fn identity_extent_killer_runs_through_the_migrated_core() {
    let p = plane("p");
    let q = plane("q");
    let small_relation = Ext::from_pairs(2, &[(0, 0), (1, 1)]);
    let large_relation = Ext::from_pairs(3, &[(0, 0), (1, 1)]);
    let small = Bank::grow_in(
        Name::from("world-relation"),
        small_relation,
        p.clone(),
        false,
    );
    let large = Bank::grow_in(
        Name::from("world-relation"),
        large_relation,
        q.clone(),
        false,
    );
    let (a, b) = witnesses(&small, &large);
    let a_large = large
        .entries
        .iter()
        .find(|entry| entry.entity.id == a.entity.id)
        .unwrap();
    let b_large = large
        .entries
        .iter()
        .find(|entry| entry.entity.id == b.entity.id)
        .unwrap();

    let mut graph = Metagraph::new();
    ingest(&mut graph, &small);
    ingest(&mut graph, &large);

    // 1–3. Different constructions survive an equal projection, including
    // the extent index which may contain further indistinguishable entities.
    assert_ne!(a.entity.id, b.entity.id);
    assert_ne!(a.entity.intension, b.entity.intension);
    assert_eq!(a.projection.extent, b.projection.extent);
    let same_extent = graph.entities_with_extent(&p, &a.projection.extent);
    assert!(same_extent.contains(&a.entity.id));
    assert!(same_extent.contains(&b.entity.id));

    // 4. The two relation occurrences independently remain endpoints.
    let relation = &small.entries[0];
    let edge_a = add_link(&mut graph, relation, a, p.clone(), "candidate-a");
    let edge_b = add_link(&mut graph, relation, b, p.clone(), "candidate-b");
    assert_ne!(edge_a, edge_b);
    assert_eq!(graph.metaedges_using(&a.entity.id).len(), 1);
    assert_eq!(graph.metaedges_using(&b.entity.id).len(), 1);

    // 5–7. Equality is local. The larger projection supplies a concrete
    // counterexample, and both q projections restrict back to p.
    let equality = add_equality(&mut graph, a, b, p.clone());
    assert!(graph.equality_active(&graph.equalities()[0]));

    // 9. Reversing independent insertion levels yields the same semantic
    // bytes. The IDs themselves contain no insertion counters.
    let mut reordered = Metagraph::new();
    ingest(&mut reordered, &large);
    ingest(&mut reordered, &small);
    add_link(&mut reordered, relation, b, p.clone(), "candidate-b");
    add_link(&mut reordered, relation, a, p.clone(), "candidate-a");
    add_equality(&mut reordered, a, b, p.clone());
    assert_eq!(graph.report(), reordered.report());

    assert_ne!(a_large.projection.extent, b_large.projection.extent);
    let mut counterexample = a_large
        .projection
        .extent
        .difference(&b_large.projection.extent);
    counterexample.extend(
        b_large
            .projection
            .extent
            .difference(&a_large.projection.extent),
    );
    assert!(!counterexample.is_empty());
    let map = [Some(0), Some(1), None];
    assert_eq!(
        a_large.projection.extent.restrict(&map, 2).unwrap(),
        a.projection.extent
    );
    assert_eq!(
        b_large.projection.extent.restrict(&map, 2).unwrap(),
        b.projection.extent
    );

    let q_equality = Evidence::new(
        ClaimId::derived("equal-at", [a.entity.id.as_str(), b.entity.id.as_str()]),
        "compare-extents",
        vec![
            a_large.projection.claim.clone(),
            b_large.projection.claim.clone(),
        ],
        Strength::Strict,
        q.clone(),
    );
    graph.add_evidence(q_equality.clone()).unwrap();
    assert!(
        graph
            .add_equal_at(a.entity.id.clone(), b.entity.id.clone(), q, q_equality.id,)
            .unwrap_err()
            .contains("not equal")
    );

    // 8. Retraction invalidates only the dependent path. Nothing is deleted:
    // the equality and both metaedges remain queryable as history.
    let refuter = Evidence::new(
        ClaimId::named("event", "refute-a"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph
        .retract(a.construction.id.clone(), refuter.id)
        .unwrap();
    assert_eq!(
        graph.evidence_state(&a.construction.id),
        Some(EvidenceState::Retracted)
    );
    assert_eq!(
        graph.evidence_state(&equality.id),
        Some(EvidenceState::Unsupported)
    );
    assert!(!graph.entity_active(&a.entity.id));
    assert!(graph.entity_active(&b.entity.id));
    assert_eq!(graph.equalities().len(), 1);
    assert_eq!(graph.metaedges().count(), 2);
    assert_eq!(
        graph
            .metaedges()
            .filter(|edge| graph.metaedge_active(edge))
            .count(),
        1
    );
}

#[test]
fn dense_and_sparse_exact_relations_have_the_same_semantic_state() {
    let bank = Bank::grow_in(
        Name::from("world-relation"),
        Ext::from_pairs(3, &[(0, 0), (1, 1)]),
        plane("q"),
        false,
    );
    let dense = exact_graph(&bank, false);
    let sparse = exact_graph(&bank, true);
    assert_eq!(dense.report(), sparse.report());
    assert_eq!(
        dense
            .entities()
            .map(|entity| &entity.id)
            .collect::<Vec<_>>(),
        sparse
            .entities()
            .map(|entity| &entity.id)
            .collect::<Vec<_>>()
    );
}

#[test]
fn journal_replay_restores_live_and_retracted_semantics() {
    let p = plane("p");
    let bank = Bank::grow_in(
        Name::from("world-relation"),
        Ext::from_pairs(2, &[(0, 0), (1, 1)]),
        p.clone(),
        false,
    );
    let (a, b) = bank
        .classes
        .iter()
        .filter_map(|class| {
            let glued: Vec<_> = class
                .iter()
                .map(|&index| &bank.entries[index])
                .filter(|entry| matches!(entry.entity.intension, Intension::Glue { .. }))
                .collect();
            (glued.len() >= 2).then(|| (glued[0], glued[1]))
        })
        .next()
        .expect("the bank has two equal glue projections");

    let mut graph = exact_graph(&bank, false);
    let equality = add_equality(&mut graph, a, b, p.clone());
    add_link(&mut graph, &bank.entries[0], a, p, "candidate-a");
    let open_intension = Intension::Glue {
        operation: "journal-open-frontier".into(),
        parts: vec![
            Part::Entity(bank.entries[0].entity.id.clone()),
            Part::Hole("missing-relation".into()),
        ],
        wiring: Vec::new(),
        interface: vec!["in".into(), "out".into()],
    };
    let provisional = agl::meta::Entity::new(open_intension.clone(), Vec::new());
    let open_evidence = Evidence::new(
        ClaimId::derived("entity", [provisional.id.as_str()]),
        "test-open-frontier",
        vec![bank.entries[0].construction.conclusion.clone()],
        Strength::Strict,
        Plane::new(),
    );
    let open = agl::meta::Entity::new(open_intension, vec![open_evidence.id.clone()]);
    graph.add_evidence(open_evidence).unwrap();
    graph.add_entity(open).unwrap();
    let refuter = Evidence::new(
        ClaimId::named("event", "refute-a"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph
        .retract(a.construction.id.clone(), refuter.id)
        .unwrap();

    let mut journal = Journal::new();
    graph.append_journal(&mut journal).unwrap();
    let text = journal.text();
    let checked = Journal::parse(&text).unwrap();
    let replayed = Metagraph::<ExactRelation>::replay_journal(&checked).unwrap();
    assert_eq!(replayed.report(), graph.report());
    assert_eq!(replayed.open_frontier(), graph.open_frontier());
    assert_eq!(
        replayed.evidence_state(&equality.id),
        Some(EvidenceState::Unsupported)
    );

    let mut replayed_journal = Journal::new();
    replayed.append_journal(&mut replayed_journal).unwrap();
    assert_eq!(replayed_journal.text(), text);
}

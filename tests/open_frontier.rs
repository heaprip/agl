//! An open composition is an ordinary first-class intension. Filling its
//! holes uses the shared proof graph; there is no Question object or solver
//! dispatch between the open and closed states.

use agl::layer::Query;
use agl::meta::{
    ClaimId, Entity, EntityId, Evidence, EvidenceState, Intension, Metaedge, Metagraph, PortBinding,
};
use agl::model::{Plane, Strength};

fn composition() -> Query {
    Query::gluings()
        .into_iter()
        .find(|query| query.to_string() == "{x,y | R(x,a), S(a,y)}")
        .expect("composition is one of the generic gluings")
}

fn add_primitive(graph: &mut Metagraph<()>, name: &str) -> (EntityId, agl::meta::EvidenceId) {
    let evidence = Evidence::new(
        ClaimId::named("input-relation", name),
        format!("input:{name}"),
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    let entity = Entity::new(
        Intension::Primitive {
            source: name.to_string(),
        },
        vec![evidence.id.clone()],
    );
    graph.add_evidence(evidence.clone()).unwrap();
    graph.add_entity(entity.clone()).unwrap();
    (entity.id, evidence.id)
}

#[test]
fn one_frontier_closes_by_the_same_operation_and_remains_reusable() {
    let mut graph = Metagraph::<()>::new();
    let (r, r_evidence) = add_primitive(&mut graph, "r");
    let (s, _) = add_primitive(&mut graph, "s");

    let open_intension = composition().open_intension();
    let provisional = Entity::new(open_intension.clone(), Vec::new());
    let open_evidence = Evidence::new(
        ClaimId::derived("entity", [provisional.id.as_str()]),
        "open-composition",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    let open = Entity::new(open_intension, vec![open_evidence.id.clone()]);
    graph.add_evidence(open_evidence).unwrap();
    graph.add_entity(open.clone()).unwrap();
    assert_eq!(
        graph.open_frontier(),
        [(
            open.id.clone(),
            vec!["hole:0".to_string(), "hole:1".to_string()]
        )]
    );

    let direct = Entity::new(composition().intension(&[r.clone(), s]), Vec::new());
    let (made, truncated) = graph.expand_open_frontier(Plane::new(), 2, 16).unwrap();
    assert!(!truncated);
    assert!(made.contains(&direct.id));
    let closed = direct.id;
    assert!(graph.entity(&closed).unwrap().intension.holes().is_empty());
    // The two possible orders of filling the holes are alternative evidence
    // for one construction, not two result entities.
    assert_eq!(graph.entity(&closed).unwrap().bases.len(), 2);

    // A closed composition immediately participates as a relation occurrence
    // in the same graph. Its evidence depends on the construction claim.
    let edge_evidence = Evidence::new(
        ClaimId::named("test", "uses-closed-composition"),
        "reuse-closed-composition",
        vec![ClaimId::derived("entity", [closed.as_str()])],
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(edge_evidence.clone()).unwrap();
    let edge = Metaedge::new(
        closed.clone(),
        vec![PortBinding::new("subject", r)],
        Plane::new(),
        &edge_evidence,
    );
    graph.add_metaedge(edge.clone()).unwrap();
    assert!(graph.metaedge_active(&edge));

    // Both construction orders ultimately depend on r. Retraction propagates
    // through the filled frontier into the relation which reused its result.
    let refuter = Evidence::new(
        ClaimId::named("event", "retract-r"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(r_evidence, refuter.id).unwrap();
    assert!(!graph.entity_active(&closed));
    assert_eq!(
        graph.evidence_state(&edge_evidence.id),
        Some(EvidenceState::Unsupported)
    );
    assert!(!graph.metaedge_active(&edge));
}

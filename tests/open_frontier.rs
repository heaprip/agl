//! An open composition is an ordinary first-class intension. Filling its
//! holes uses the shared proof graph; there is no Question object or solver
//! dispatch between the open and closed states.

use agl::layer::Query;
use agl::meta::{
    ClaimId, Entity, EntityId, Evidence, EvidenceState, Intension, Metaedge, Metagraph, PortBinding,
};
use agl::model::{Plane, Strength};
use agl::plane::Axes;

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

fn add_situated_primitive(
    graph: &mut Metagraph<()>,
    name: &str,
    context: Plane,
) -> (EntityId, agl::meta::EvidenceId) {
    let evidence = Evidence::new(
        ClaimId::named("input-relation", name),
        format!("input:{name}"),
        Vec::new(),
        Strength::Strict,
        context,
    );
    let entity = Entity::new(
        Intension::Primitive {
            source: name.to_string(),
        },
        vec![evidence.id.clone()],
    );
    graph.add_evidence(evidence).unwrap();
    graph.add_entity(entity.clone()).unwrap();
    (entity.id, entity.bases[0].clone())
}

fn axis_context(value: &str) -> Plane {
    Plane::from([("domain".to_string(), value.to_string())])
}

fn single_hole_glue() -> Intension {
    Intension::Glue {
        operation: "test-glue".to_string(),
        parts: vec![agl::meta::Part::Hole("hole".to_string())],
        wiring: Vec::new(),
        interface: Vec::new(),
    }
}

#[test]
fn explicit_bind_closes_at_the_meet_of_overlapping_evidence_contexts() {
    let mut axes = Axes::default();
    axes.declare_axis("domain");
    axes.declare_value("domain", "p", None).unwrap();
    axes.declare_value("domain", "q", None).unwrap();
    axes.declare_overlap("domain", "p", "q").unwrap();
    let mut graph = Metagraph::<()>::new();
    let open_intension = single_hole_glue();
    let open_evidence = Evidence::new(
        ClaimId::derived(
            "entity",
            [Entity::new(open_intension.clone(), Vec::new()).id.as_str()],
        ),
        "open-composition",
        Vec::new(),
        Strength::Strict,
        axis_context("p"),
    );
    let open = Entity::new(open_intension, vec![open_evidence.id.clone()]);
    graph.add_evidence(open_evidence).unwrap();
    graph.add_entity(open.clone()).unwrap();
    let (part, part_evidence) = add_situated_primitive(&mut graph, "part", axis_context("q"));

    let made = graph
        .bind_open_at_meets(&axes, &open.id, "hole", &part)
        .unwrap();
    let meet = axis_context("p∩q");
    assert_eq!(
        made,
        vec![(
            meet.clone(),
            Entity::new(
                open.intension.bind("hole", part.clone()).unwrap(),
                Vec::new()
            )
            .id
        )]
    );
    let closed = graph.entity(&made[0].1).unwrap();
    assert!(closed.intension.holes().is_empty());
    let evidence = graph
        .evidence()
        .find(|e| e.context == meet)
        .unwrap()
        .clone();
    assert_eq!(evidence.premises.len(), 2);
    assert_eq!(
        graph.evidence_state_with_axes(&axes, &evidence.id),
        Some(EvidenceState::Active)
    );
    assert!(graph.entity_active_with_axes(&axes, &made[0].1));

    let refuter = Evidence::new(
        ClaimId::named("event", "retract-contextual-part"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(part_evidence, refuter.id).unwrap();
    assert_eq!(
        graph.evidence_state_with_axes(&axes, &evidence.id),
        Some(EvidenceState::Unsupported)
    );
    assert!(!graph.entity_active_with_axes(&axes, &made[0].1));
}

#[test]
fn explicit_bind_leaves_hole_open_when_contexts_are_disjoint() {
    let mut axes = Axes::default();
    axes.declare_axis("domain");
    axes.declare_value("domain", "p", None).unwrap();
    axes.declare_value("domain", "q", None).unwrap();
    let mut graph = Metagraph::<()>::new();
    let open_intension = single_hole_glue();
    let open_evidence = Evidence::new(
        ClaimId::derived(
            "entity",
            [Entity::new(open_intension.clone(), Vec::new()).id.as_str()],
        ),
        "open-composition",
        Vec::new(),
        Strength::Strict,
        axis_context("p"),
    );
    let open = Entity::new(open_intension, vec![open_evidence.id.clone()]);
    graph.add_evidence(open_evidence).unwrap();
    graph.add_entity(open.clone()).unwrap();
    let (part, _) = add_situated_primitive(&mut graph, "part", axis_context("q"));
    let before_entities = graph.entities().count();
    let before_evidence = graph.evidence().count();

    assert!(
        graph
            .bind_open_at_meets(&axes, &open.id, "hole", &part)
            .unwrap()
            .is_empty()
    );
    assert_eq!(graph.entities().count(), before_entities);
    assert_eq!(graph.evidence().count(), before_evidence);
    assert_eq!(
        graph.entity(&open.id).unwrap().intension.holes(),
        ["hole"].into_iter().collect()
    );
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

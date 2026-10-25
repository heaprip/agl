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
    graph.add_evidence(open_evidence.clone()).unwrap();
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
    graph.add_evidence(open_evidence.clone()).unwrap();
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
fn metaedge_activation_binds_only_its_named_target_and_retracts() {
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
    graph.add_evidence(open_evidence.clone()).unwrap();
    graph.add_entity(open.clone()).unwrap();
    let (chosen, chosen_evidence) = add_situated_primitive(&mut graph, "chosen", axis_context("q"));
    let (decoy, _) = add_situated_primitive(&mut graph, "decoy", axis_context("q"));
    let meet = axis_context("p∩q");
    let activation_evidence = Evidence::new(
        ClaimId::named("test", "activate-chosen"),
        "activation",
        vec![
            open_evidence.conclusion.clone(),
            chosen_evidence_conclusion(&graph, &chosen_evidence),
        ],
        Strength::Strict,
        meet.clone(),
    );
    graph.add_evidence(activation_evidence.clone()).unwrap();
    let activation = Metaedge::new(
        open.id.clone(),
        vec![PortBinding::new("hole", chosen.clone())],
        meet,
        &activation_evidence,
    );
    graph.add_metaedge(activation.clone()).unwrap();

    let made = graph.activate_open_frontier(&axes).unwrap();
    let expected = Entity::new(
        open.intension.bind("hole", chosen.clone()).unwrap(),
        Vec::new(),
    )
    .id;
    assert_eq!(made, vec![(axis_context("p∩q"), expected.clone())]);
    assert_eq!(
        graph.entity(&expected).unwrap().intension.dependencies(),
        vec![&chosen]
    );
    assert!(
        !graph
            .entity(&expected)
            .unwrap()
            .intension
            .dependencies()
            .contains(&&decoy)
    );
    assert!(graph.metaedge_active_with_axes(&axes, &activation));

    let result_evidence = graph.entity(&expected).unwrap().bases[0].clone();
    let result_support = graph
        .evidence()
        .find(|evidence| evidence.id == result_evidence)
        .unwrap();
    assert_eq!(result_support.context, axis_context("p∩q"));
    assert_eq!(result_support.premises.len(), 3);
    assert!(
        result_support
            .premises
            .contains(&activation_evidence.conclusion)
    );
    let refuter = Evidence::new(
        ClaimId::named("event", "retract-activation"),
        "refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(activation_evidence.id, refuter.id).unwrap();
    assert_eq!(
        graph.evidence_state_with_axes(&axes, &result_evidence),
        Some(EvidenceState::Unsupported)
    );
}

#[test]
fn metaedge_activation_rejects_unknown_role_without_mutation() {
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
        Plane::new(),
    );
    let open = Entity::new(open_intension, vec![open_evidence.id.clone()]);
    graph.add_evidence(open_evidence.clone()).unwrap();
    graph.add_entity(open.clone()).unwrap();
    let (target, _) = add_primitive(&mut graph, "target");
    let activation_evidence = Evidence::new(
        ClaimId::named("test", "bad-role"),
        "activation",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(activation_evidence.clone()).unwrap();
    let activation = Metaedge::new(
        open.id.clone(),
        vec![PortBinding::new("unknown", target)],
        Plane::new(),
        &activation_evidence,
    );
    graph.add_metaedge(activation.clone()).unwrap();
    let entity_count = graph.entities().count();
    let evidence_count = graph.evidence().count();

    let error = graph
        .bind_open_from_metaedge(&Axes::default(), &activation.entity.id)
        .unwrap_err();
    assert!(error.contains("not a hole"));
    assert_eq!(graph.entities().count(), entity_count);
    assert_eq!(graph.evidence().count(), evidence_count);
    assert_eq!(
        graph.entity(&open.id).unwrap().intension.holes(),
        ["hole"].into_iter().collect()
    );
}

#[test]
fn metaedge_activation_respects_its_own_disjoint_context() {
    let mut axes = Axes::default();
    axes.declare_axis("domain");
    axes.declare_value("domain", "p", None).unwrap();
    axes.declare_value("domain", "q", None).unwrap();
    axes.declare_value("domain", "r", None).unwrap();
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
    let (target, _) = add_situated_primitive(&mut graph, "disjoint-target", axis_context("q"));
    let activation_evidence = Evidence::new(
        ClaimId::named("test", "disjoint-activation"),
        "activation",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(activation_evidence.clone()).unwrap();
    let activation = Metaedge::new(
        open.id.clone(),
        vec![PortBinding::new("hole", target)],
        axis_context("r"),
        &activation_evidence,
    );
    graph.add_metaedge(activation.clone()).unwrap();
    let entity_count = graph.entities().count();
    let evidence_count = graph.evidence().count();

    assert!(graph.activate_open_frontier(&axes).unwrap().is_empty());
    assert_eq!(graph.entities().count(), entity_count);
    assert_eq!(graph.evidence().count(), evidence_count);
    assert_eq!(
        graph.entity(&open.id).unwrap().intension.holes(),
        ["hole"].into_iter().collect()
    );
}

fn chosen_evidence_conclusion(graph: &Metagraph<()>, id: &agl::meta::EvidenceId) -> ClaimId {
    graph
        .evidence()
        .find(|evidence| &evidence.id == id)
        .unwrap()
        .conclusion
        .clone()
}

#[test]
fn one_frontier_closes_by_the_same_operation_and_remains_reusable() {
    let mut graph = Metagraph::<()>::new();
    let (r, r_evidence) = add_primitive(&mut graph, "r");
    let (s, s_evidence) = add_primitive(&mut graph, "s");

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
    graph.add_evidence(open_evidence.clone()).unwrap();
    graph.add_entity(open.clone()).unwrap();
    assert_eq!(
        graph.open_frontier(),
        [(
            open.id.clone(),
            vec!["hole:0".to_string(), "hole:1".to_string()]
        )]
    );

    let activation_evidence = Evidence::new(
        ClaimId::named("test", "activate-open-composition"),
        "activate-open-composition",
        vec![
            open_evidence.conclusion.clone(),
            graph
                .evidence()
                .find(|e| e.id == r_evidence)
                .unwrap()
                .conclusion
                .clone(),
            graph
                .evidence()
                .find(|e| e.id == s_evidence)
                .unwrap()
                .conclusion
                .clone(),
        ],
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(activation_evidence.clone()).unwrap();
    let activation = Metaedge::new(
        open.id.clone(),
        vec![
            PortBinding::new("hole:0", r.clone()),
            PortBinding::new("hole:1", s.clone()),
        ],
        Plane::new(),
        &activation_evidence,
    );
    graph.add_metaedge(activation.clone()).unwrap();
    assert!(graph.metaedge_active(&activation));
    let made = graph.activate_open_frontier(&Axes::default()).unwrap();
    let direct = Entity::new(composition().intension(&[r.clone(), s]), Vec::new());
    assert_eq!(made, vec![(Plane::new(), direct.id.clone())]);
    let closed = direct.id;
    assert!(graph.entity(&closed).unwrap().intension.holes().is_empty());
    assert_eq!(graph.entity(&closed).unwrap().bases.len(), 1);

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

    // Retraction propagates through the activation and the result into the
    // relation which reused that result.
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
        graph.evidence_state(&activation_evidence.id),
        Some(EvidenceState::Unsupported)
    );
    assert_eq!(
        graph.evidence_state(&edge_evidence.id),
        Some(EvidenceState::Unsupported)
    );
    assert!(!graph.metaedge_active(&edge));
}

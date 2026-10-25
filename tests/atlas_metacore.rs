//! Integration seam: generic atlas model candidates become proof-relevant
//! structural occurrences in the shared metacore. This is not the full
//! `quaternions_from_soup` search.

use agl::atlas::{self, Law, Table, models_sat};
use agl::meta::{
    ClaimId, Entity, Evidence, EvidenceState, Intension, Metaedge, Metagraph, PortBinding,
};
use agl::model::{Plane, Strength};

const ASSOC: &str = "∀x∀y∀z: x·(y·z) = (x·y)·z";
const LEFT: &str = "∀x∀y∃z: x = y·z";
const RIGHT: &str = "∀x∀y∃z: x = z·y";

fn op(table: &Table, a: u8, b: u8) -> u8 {
    table.get(a, b).unwrap()
}

fn commutative(table: &Table) -> bool {
    (0..table.n).all(|a| (0..table.n).all(|b| op(table, a, b) == op(table, b, a)))
}

fn nontrivial_involutions(table: &Table) -> usize {
    let unit = (0..table.n)
        .find(|&e| (0..table.n).all(|x| op(table, e, x) == x && op(table, x, e) == x))
        .unwrap();
    (0..table.n)
        .filter(|&x| x != unit && op(table, x, x) == unit)
        .count()
}

fn law<'a>(laws: &'a [Law], description: &str) -> &'a Law {
    laws.iter()
        .find(|law| law.to_string() == description)
        .unwrap_or_else(|| panic!("atlas language has no law `{description}`"))
}

fn add_relation(graph: &mut Metagraph<Table>) -> agl::meta::EntityId {
    let evidence = Evidence::new(
        ClaimId::named("test-relation", "candidate-model"),
        "test-input-relation",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    let entity = Entity::new(
        Intension::Primitive {
            source: "candidate-model-relation".into(),
        },
        vec![evidence.id.clone()],
    );
    graph.add_evidence(evidence).unwrap();
    graph.add_entity(entity.clone()).unwrap();
    entity.id
}

#[test]
fn generic_order_eight_candidates_enter_metacore_with_q8_provenance() {
    let language = atlas::language();
    let laws = [
        law(&language, LEFT),
        law(&language, RIGHT),
        law(&language, ASSOC),
    ];

    // This is the generic finite-model search used by the atlas' own s_entities(8).
    let tables: Vec<Table> = (1..=8)
        .flat_map(|order| models_sat(order, &laws, &[]).0)
        .collect();
    let factorizations = atlas::splits(&tables);
    let q8: Vec<_> = tables
        .iter()
        .enumerate()
        .filter(|(i, table)| {
            table.n == 8
                && factorizations[*i].is_empty()
                && !commutative(table)
                && nontrivial_involutions(table) == 1
        })
        .collect();
    assert_eq!(q8.len(), 1, "the atlas' structural Q8 criterion");
    let q8_table = q8[0].1;

    let mut graph = Metagraph::<Table>::new();
    let ids = atlas::record_models(&mut graph, &tables, &laws, Plane::new()).unwrap();
    assert_eq!(ids.len(), tables.len());
    let mut reversed_tables = tables.clone();
    reversed_tables.reverse();
    let reversed_laws = [laws[2], laws[1], laws[0]];
    let mut reordered = Metagraph::<Table>::new();
    atlas::record_models(
        &mut reordered,
        &reversed_tables,
        &reversed_laws,
        Plane::new(),
    )
    .unwrap();
    assert_eq!(graph.report(), reordered.report());
    let q8_id = graph
        .projections()
        .find(|projection| projection.extent == *q8_table)
        .unwrap()
        .entity
        .clone();
    let q8_entity = graph.entity(&q8_id).unwrap();
    let Intension::Glue { parts, .. } = &q8_entity.intension else {
        panic!("atlas candidates must keep their structural cell presentation")
    };
    assert_eq!(parts.len(), 64);
    assert_eq!(graph.extent(&q8_id, &Plane::new()), Some(q8_table));
    let construction = graph
        .evidence()
        .find(|evidence| q8_entity.bases.contains(&evidence.id))
        .unwrap();
    assert_eq!(construction.operation, "atlas-model-from-laws");
    for input_law in &laws {
        let description = input_law.to_string();
        assert!(
            construction
                .premises
                .contains(&ClaimId::named("atlas-law", &description))
        );
    }

    // Every candidate has its own presentation identity, and the selected
    // model can immediately be used as a first-class metaedge port.
    assert!(ids.contains(&q8_id));
    let relation = add_relation(&mut graph);
    let edge_evidence = Evidence::new(
        ClaimId::named("test", "uses-atlas-model"),
        "use-atlas-model-as-endpoint",
        vec![ClaimId::derived("entity", [q8_id.as_str()])],
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(edge_evidence.clone()).unwrap();
    let edge = Metaedge::new(
        relation,
        vec![PortBinding::new("model", q8_id.clone())],
        Plane::new(),
        &edge_evidence,
    );
    graph.add_metaedge(edge.clone()).unwrap();
    assert!(graph.metaedge_active(&edge));
    assert!(
        graph
            .metaedges_using(&q8_id)
            .into_iter()
            .any(|candidate| candidate == &edge)
    );

    // The table presentation remains in history, but acceptance as a model
    // and every dependent use fall when one of its input laws is retracted.
    let associative = graph
        .evidence()
        .find(|evidence| evidence.operation == format!("atlas-input-law:{ASSOC}"))
        .unwrap()
        .id
        .clone();
    let refuter = Evidence::new(
        ClaimId::named("event", "retract-associativity"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(associative, refuter.id).unwrap();
    assert!(!graph.entity_active(&q8_id));
    assert_eq!(
        graph.evidence_state(&edge_evidence.id),
        Some(EvidenceState::Unsupported)
    );
    assert!(!graph.metaedge_active(&edge));
}

#[test]
fn recording_rejects_a_nonmodel_before_mutating_the_metagraph() {
    let language = atlas::language();
    let left = law(&language, LEFT);
    let constant = Table {
        n: 2,
        cells: vec![Some(0); 4],
    };
    let mut graph = Metagraph::<Table>::new();
    let error = atlas::record_models(&mut graph, &[constant], &[left], Plane::new())
        .expect_err("a constant table is not a quasigroup model");
    assert!(error.contains("does not satisfy input law"), "{error}");
    assert_eq!(graph.entities().count(), 0);
    assert_eq!(graph.evidence().count(), 0);
}

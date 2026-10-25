//! Architectural killer test: identity is not a context-indexed extent.

use std::collections::BTreeMap;

use agl::bank::{Ext, Shape};
use agl::journal::Journal;
use agl::metagraph::{
    EntityId, EvidenceId, EvidenceState, ExactRelation, Intension, Metagraph, Operation, PortRef,
    Projection, Restriction,
};
use agl::model::{Plane, Strength};

fn id(name: &str) -> EntityId {
    EntityId::new(name)
}

fn ev(name: &str) -> EvidenceId {
    EvidenceId::new(name)
}

fn plane(name: &str) -> Plane {
    BTreeMap::from([("world".into(), name.into())])
}

fn add_input(graph: &mut Metagraph, name: &str) {
    graph
        .add_evidence(
            ev(name),
            vec![],
            Operation::Input(name.into()),
            Strength::Strict,
        )
        .unwrap();
}

fn add_derived(graph: &mut Metagraph, name: &str, premises: &[&str], op: Operation) {
    graph
        .add_evidence(
            ev(name),
            premises.iter().map(|p| ev(p)).collect(),
            op,
            Strength::Strict,
        )
        .unwrap();
}

fn add_primitive(graph: &mut Metagraph, name: &str) {
    graph
        .add_entity(
            id(name),
            Intension::Primitive {
                source: name.into(),
            },
            vec![ev(&format!("source-{name}"))],
        )
        .unwrap();
}

fn glue(left: &str, right: &str) -> Intension {
    Intension::Glue {
        parts: vec![id(left), id(right)],
        identifications: vec![(PortRef::new(id(left), "out"), PortRef::new(id(right), "in"))],
        interface: vec![PortRef::new(id(left), "in"), PortRef::new(id(right), "out")],
    }
}

/// The existing relation executor supplies the projections. `a` composes two
/// identities; `b` composes the world relation with identity. They coincide
/// when the world relation is identity and diverge when it lacks one pair.
fn computed_extents(n: usize, world_pairs: &[(usize, usize)], sparse: bool) -> [ExactRelation; 2] {
    let relation = Ext::from_pairs(n, world_pairs);
    // MERGES[3] joins the output of the left shape to the input of the right;
    // heads (0,3) keep the outer boundary: ordinary relational composition.
    let a = Shape::glue(&Shape::id(), &Shape::id(), 3, (0, 3));
    let b = Shape::glue(&Shape::rel(), &Shape::id(), 3, (0, 3));
    assert!(!a.same(&b), "CQ core must not identify the two intensions");
    [&a, &b].map(|shape| {
        let dense = shape.eval(&relation);
        assert_eq!(
            dense_pairs(&dense),
            reference_eval(shape, &relation),
            "existing bank executor disagrees with tuple enumeration"
        );
        if sparse {
            ExactRelation::sparse(n, &dense_pairs(&dense)).unwrap()
        } else {
            ExactRelation::from_dense(dense)
        }
    })
}

fn dense_pairs(extent: &Ext) -> Vec<(usize, usize)> {
    (0..extent.n())
        .flat_map(|a| (0..extent.n()).filter_map(move |b| extent.get(a, b).then_some((a, b))))
        .collect()
}

/// Deliberately slow reference evaluator for a finite conjunctive query.
fn reference_eval(shape: &Shape, relation: &Ext) -> Vec<(usize, usize)> {
    let n = relation.n();
    let mut values = vec![0usize; shape.vars as usize];
    let mut out = Vec::new();
    'assignments: loop {
        if shape
            .atoms
            .iter()
            .all(|&(a, b)| relation.get(values[a as usize], values[b as usize]))
        {
            out.push((values[shape.head.0 as usize], values[shape.head.1 as usize]));
        }
        for position in (0..values.len()).rev() {
            values[position] += 1;
            if values[position] < n {
                continue 'assignments;
            }
            values[position] = 0;
        }
        break;
    }
    out.sort();
    out.dedup();
    out
}

/// Build the same semantic state in two opposite topological orders and with
/// the two exact-relation representations.
fn world(reverse: bool, sparse: bool) -> Metagraph {
    let mut graph = Metagraph::new();
    let mut inputs = vec![
        "source-a-left",
        "source-a-right",
        "source-b-left",
        "source-b-right",
        "source-uses",
        "observation-p",
        "observation-q",
        "map-q-p",
        "refuter-a",
    ];
    if reverse {
        inputs.reverse();
    }
    for input in inputs {
        add_input(&mut graph, input);
    }

    let mut primitives = vec!["a-left", "a-right", "b-left", "b-right", "uses"];
    if reverse {
        primitives.reverse();
    }
    for primitive in primitives {
        add_primitive(&mut graph, primitive);
    }

    let mut builds = vec![
        ("a-build", vec!["source-a-left", "source-a-right"]),
        ("b-build", vec!["source-b-left", "source-b-right"]),
    ];
    if reverse {
        builds.reverse();
    }
    for (name, premises) in builds {
        add_derived(&mut graph, name, &premises, Operation::Build);
    }

    let mut constructions = vec![
        ("a", "a-left", "a-right", "a-build"),
        ("b", "b-left", "b-right", "b-build"),
    ];
    if reverse {
        constructions.reverse();
    }
    for (name, left, right, basis) in constructions {
        graph
            .add_entity(id(name), glue(left, right), vec![ev(basis)])
            .unwrap();
    }

    let mut observations = vec![
        ("a-p", vec!["a-build", "observation-p"]),
        ("b-p", vec!["b-build", "observation-p"]),
        ("a-q", vec!["a-build", "observation-q"]),
        ("b-q", vec!["b-build", "observation-q"]),
    ];
    if reverse {
        observations.reverse();
    }
    for (name, premises) in observations {
        add_derived(&mut graph, name, &premises, Operation::Observe);
    }

    let p = plane("p");
    let q = plane("q");
    let [a_p, b_p] = computed_extents(2, &[(0, 0), (1, 1)], sparse);
    let [a_q, b_q] = computed_extents(3, &[(0, 0), (1, 1)], sparse);
    let mut projections = vec![
        Projection {
            entity: id("a"),
            context: p.clone(),
            extent: a_p,
            evidence: ev("a-p"),
        },
        Projection {
            entity: id("b"),
            context: p.clone(),
            extent: b_p,
            evidence: ev("b-p"),
        },
        Projection {
            entity: id("a"),
            context: q.clone(),
            extent: a_q,
            evidence: ev("a-q"),
        },
        Projection {
            entity: id("b"),
            context: q.clone(),
            extent: b_q,
            evidence: ev("b-q"),
        },
    ];
    if reverse {
        projections.reverse();
    }
    for projection in projections {
        graph.add_projection(projection).unwrap();
    }

    add_derived(&mut graph, "equal-p", &["a-p", "b-p"], Operation::Compare);
    graph
        .add_equal_at(id("a"), id("b"), p.clone(), ev("equal-p"))
        .unwrap();

    let mut links = vec![
        ("link-a", "a-build", "edge-a", "a"),
        ("link-b", "b-build", "edge-b", "b"),
    ];
    if reverse {
        links.reverse();
    }
    for (evidence, construction, edge, endpoint) in links {
        add_derived(
            &mut graph,
            evidence,
            &["source-uses", construction],
            Operation::Link,
        );
        graph
            .add_metaedge(
                id(edge),
                id("uses"),
                vec![("subject".into(), id(endpoint))],
                p.clone(),
                ev(evidence),
            )
            .unwrap();
    }

    graph
        .add_restriction(Restriction {
            from: q,
            to: p,
            point_map: vec![Some(0), Some(1), None],
            target_n: 2,
            evidence: ev("map-q-p"),
        })
        .unwrap();
    graph
}

#[test]
fn identity_extent_killer() {
    let mut graph = world(false, false);
    let (a, b) = (id("a"), id("b"));
    let (p, q) = (plane("p"), plane("q"));

    // 1. Identity and construction do not come from an extent.
    assert_ne!(a, b);
    assert_ne!(
        graph.entity(&a).unwrap().intension,
        graph.entity(&b).unwrap().intension
    );

    // 2–3. Equal projection, but the extent index returns both occurrences.
    assert_eq!(graph.extent(&a, &p).unwrap(), graph.extent(&b, &p).unwrap());
    assert_eq!(
        graph.entities_with_extent(&p, graph.extent(&a, &p).unwrap()),
        vec![a.clone(), b.clone()]
    );

    // 4. Relations are independently usable as endpoints of later relations.
    assert_eq!(graph.metaedges_using(&a)[0].id, id("edge-a"));
    assert_eq!(graph.metaedges_using(&b)[0].id, id("edge-b"));
    assert_ne!(
        graph.metaedges_using(&a)[0].id,
        graph.metaedges_using(&b)[0].id
    );

    // 5–6. EqualAt is local evidence; q exposes one minimal counterexample.
    assert_eq!(graph.active_equalities().len(), 1);
    assert_eq!(graph.active_equalities()[0].context, p);
    assert_ne!(graph.extent(&a, &q).unwrap(), graph.extent(&b, &q).unwrap());
    assert_eq!(
        graph
            .extent(&a, &q)
            .unwrap()
            .difference(graph.extent(&b, &q).unwrap()),
        vec![(2, 2)]
    );
    add_derived(&mut graph, "equal-q", &["a-q", "b-q"], Operation::Compare);
    assert!(
        graph
            .add_equal_at(a.clone(), b.clone(), q.clone(), ev("equal-q"))
            .unwrap_err()
            .contains("are not equal"),
        "local equality at p must not become global congruence"
    );

    // 7. The declared q -> p restriction reproduces both stored projections.
    assert_eq!(
        graph.restricted_projection(&a, &q, &p).unwrap(),
        *graph.extent(&a, &p).unwrap()
    );
    assert_eq!(
        graph.restricted_projection(&b, &q, &p).unwrap(),
        *graph.extent(&b, &p).unwrap()
    );

    // 8. Retract only a's path. History stays, dependent evidence becomes
    // unsupported, and b remains usable.
    graph.retract(&ev("a-build"), &ev("refuter-a")).unwrap();
    assert_eq!(
        graph.evidence_state(&ev("a-build")),
        Some(EvidenceState::Retracted)
    );
    for dependent in ["a-p", "a-q", "equal-p", "equal-q", "link-a"] {
        assert_eq!(
            graph.evidence_state(&ev(dependent)),
            Some(EvidenceState::Unsupported),
            "{dependent}"
        );
    }
    assert_eq!(
        graph.evidence_state(&ev("b-build")),
        Some(EvidenceState::Active)
    );
    assert!(!graph.entity_active(&a));
    assert!(graph.entity_active(&b));
    assert!(graph.active_equalities().is_empty());
    assert_eq!(
        graph.equalities().len(),
        1,
        "historical equality is retained"
    );
    assert_eq!(graph.active_metaedges()[0].id, id("edge-b"));
    assert_eq!(
        graph.metaedges().count(),
        2,
        "historical metaedge is retained"
    );
    assert!(
        graph
            .report()
            .contains("projection a inactive at={world:p}")
    );
}

#[test]
fn report_is_independent_of_input_order_and_exact_representation() {
    // 9–10. Reverse every independent construction level and replace dense
    // relations with sparse ones: semantic bytes and identities are unchanged.
    let dense = world(false, false);
    let sparse_reversed = world(true, true);
    assert_eq!(dense.report(), sparse_reversed.report());
    assert_eq!(
        dense.entities_with_extent(&plane("p"), dense.extent(&id("a"), &plane("p")).unwrap()),
        vec![id("a"), id("b")]
    );
}

#[test]
fn journal_round_trip_preserves_the_immutable_history() {
    let mut graph = world(false, false);
    graph.retract(&ev("a-build"), &ev("refuter-a")).unwrap();
    let text = graph.journal().text();
    let replayed = Journal::parse(&text).unwrap();
    assert_eq!(replayed.text(), text);
    assert!(text.contains(" retraction retract direct "));
    assert!(text.contains("target=a-build by=refuter-a"));
}

#[test]
fn retracting_each_input_invalidates_exactly_its_evidence_descendants() {
    for target in [
        "source-a-left",
        "source-a-right",
        "source-b-left",
        "source-b-right",
        "source-uses",
        "observation-p",
        "observation-q",
        "map-q-p",
    ] {
        let mut graph = world(false, false);
        let ids = graph.evidence_ids().cloned().collect::<Vec<_>>();
        let affected = ids
            .iter()
            .filter(|id| graph.evidence_depends_on(id, &ev(target)))
            .cloned()
            .collect::<Vec<_>>();
        graph.retract(&ev(target), &ev("refuter-a")).unwrap();
        for evidence in ids {
            let expected = if evidence == ev(target) {
                EvidenceState::Retracted
            } else if affected.contains(&evidence) {
                EvidenceState::Unsupported
            } else {
                EvidenceState::Active
            };
            assert_eq!(
                graph.evidence_state(&evidence),
                Some(expected),
                "target={target}, evidence={evidence}"
            );
        }
    }
}

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

#[test]
fn dsl_metaedge_references_relation_occurrences_not_symbols() {
    let src = "
fact relation_occ: relation_object(name: observes) @
fact target_occ: object(name: sample) @
metaedge first: &relation_occ(subject: &target_occ) @
metaedge second: &first(subject: &target_occ) @
";
    let out = evaluate(&agl::parse(src).unwrap(), &Plane::new());
    assert!(out.errors.is_empty(), "{:?}", out.errors);
    assert_eq!(out.metaedges.len(), 2);

    let fact_entity = |source: &str| {
        out.db
            .values()
            .flat_map(|(_, derivations)| derivations)
            .find(|derivation| derivation.source() == source)
            .unwrap()
            .entity
            .id
            .clone()
    };
    let relation = fact_entity("relation_occ");
    let target = fact_entity("target_occ");
    let first = out
        .metaedges
        .iter()
        .find(|edge| {
            matches!(
                &edge.entity.intension,
                Intension::Metaedge { source, .. } if source == "first"
            )
        })
        .unwrap();
    let second = out
        .metaedges
        .iter()
        .find(|edge| {
            matches!(
                &edge.entity.intension,
                Intension::Metaedge { source, .. } if source == "second"
            )
        })
        .unwrap();
    assert_eq!(first.relation, relation);
    assert_eq!(first.ports[0].target, target);
    assert_eq!(second.relation, first.entity.id);
    assert_eq!(second.ports[0].target, target);

    let graph = out.metagraph().unwrap();
    assert_eq!(graph.metaedges_using(&target).len(), 2);
    assert!(graph.metaedges().all(|edge| graph.metaedge_active(edge)));
    let report = agl::run(&agl::parse(src).unwrap());
    assert_eq!(report.metaedges.len(), 2);
    assert_eq!(agl::render(&report).matches("metaedge ").count(), 2);
}

#[test]
fn dsl_metaedges_are_contextual_and_order_independent() {
    let declarations = "
axis world
value world p
value world q
fact relation_occ: relation_object(name: observes) @
fact target_occ: object(name: sample) @
";
    let forward = format!(
        "{declarations}\
         metaedge first: &relation_occ(subject: &target_occ) @ world:p\n\
         metaedge second: &first(subject: &target_occ) @ world:p\n"
    );
    let reverse = format!(
        "{declarations}\
         metaedge second: &first(subject: &target_occ) @ world:p\n\
         metaedge first: &relation_occ(subject: &target_occ) @ world:p\n"
    );
    let p = Plane::from([("world".into(), "p".into())]);
    let q = Plane::from([("world".into(), "q".into())]);
    let a = evaluate(&agl::parse(&forward).unwrap(), &p);
    let b = evaluate(&agl::parse(&reverse).unwrap(), &p);
    assert_eq!(
        a.metagraph().unwrap().report(),
        b.metagraph().unwrap().report()
    );
    assert_eq!(a.metaedges.len(), 2);
    assert!(
        evaluate(&agl::parse(&forward).unwrap(), &Plane::new())
            .metaedges
            .is_empty()
    );
    assert!(
        evaluate(&agl::parse(&forward).unwrap(), &q)
            .metaedges
            .is_empty()
    );
}

#[test]
fn ordinary_rules_and_queries_compute_over_metaedges() {
    let src = "
relation seen(target)
fact relation_occ: relation_object(name: observes) @
fact target_occ: object(name: sample) @
metaedge first: &relation_occ(subject: &target_occ) @
rule sees strict @: seen(target: ?target) <- metaedge(relation: &relation_occ, subject: ?target)
query metaedge(relation: &relation_occ, subject: &target_occ) @ expect yes
query seen(target: &target_occ) @ expect yes
";
    let prog = agl::parse(src).unwrap();
    let report = agl::run(&prog);
    assert!(!report.has_errors(), "{}", agl::render(&report));
    assert_eq!(
        report.failed_queries().count(),
        0,
        "{}",
        agl::render(&report)
    );

    let out = evaluate(&prog, &Plane::new());
    let (_, seen) = out
        .db
        .values()
        .find(|(atom, _)| atom.rel == "seen")
        .unwrap();
    assert_eq!(seen.len(), 1);
    assert_eq!(seen[0].source(), "sees");
    assert_eq!(seen[0].evidence.premises.len(), 1);

    // The normal rule derivation depends on the metaedge claim in the same
    // AND/OR graph, so retracting the link invalidates the consequence.
    let mut graph = out.metagraph().unwrap();
    let link = out
        .meta_evidence
        .iter()
        .find(|evidence| evidence.operation == "first")
        .unwrap()
        .id
        .clone();
    let conclusion = seen[0].evidence.id.clone();
    let refuter = Evidence::new(
        ClaimId::named("event", "refute-first"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(link, refuter.id).unwrap();
    assert_eq!(
        graph.evidence_state(&conclusion),
        Some(EvidenceState::Unsupported)
    );
}

#[test]
fn rule_heads_construct_reusable_first_class_metaedges() {
    let src = "
relation candidate(relation, target)
fact relation_occ: relation_object(name: observes) @
fact target_occ: object(name: sample) @
fact candidate_occ: candidate(relation: &relation_occ, target: &target_occ) @
rule construct strict @: metaedge(relation: ?relation, subject: ?target) <- candidate(relation: ?relation, target: ?target)
rule lift strict @: metaedge(relation: ?edge, subject: ?target) <- metaedge(occurrence: ?edge, relation: ?base, subject: ?target), candidate(relation: ?base, target: ?target)
query metaedge(relation: &relation_occ, subject: &target_occ) @ expect yes
";
    let prog = agl::parse(src).unwrap();
    let report = agl::run(&prog);
    assert!(!report.has_errors(), "{}", agl::render(&report));
    assert_eq!(
        report.failed_queries().count(),
        0,
        "{}",
        agl::render(&report)
    );

    let out = evaluate(&prog, &Plane::new());
    assert!(out.errors.is_empty(), "{:?}", out.errors);
    assert_eq!(out.metaedges.len(), 2);

    let occurrence = |source: &str| {
        out.db
            .values()
            .flat_map(|(_, derivations)| derivations)
            .find(|derivation| derivation.source() == source)
            .unwrap()
            .entity
            .id
            .clone()
    };
    let relation = occurrence("relation_occ");
    let target = occurrence("target_occ");
    let root = out
        .metaedges
        .iter()
        .find(|edge| edge.relation == relation)
        .unwrap();
    let nested = out
        .metaedges
        .iter()
        .find(|edge| edge.relation == root.entity.id)
        .unwrap();
    assert_eq!(root.ports[0].target, target);
    assert_eq!(nested.ports[0].target, target);

    let root_atom = out
        .db
        .values()
        .find(|(_, derivations)| {
            derivations
                .iter()
                .any(|derivation| derivation.entity.id == root.entity.id)
        })
        .map(|(atom, _)| atom)
        .unwrap();
    assert!(root_atom.args.iter().any(|(role, term)| {
        role == agl::model::METAEDGE_OCCURRENCE_ROLE && matches!(term, agl::model::Term::Ref(_))
    }));

    // The second edge's evidence uses the first edge's claim. Retraction is
    // therefore semantic, not merely removal from the report.
    let mut graph = out.metagraph().unwrap();
    let refuter = Evidence::new(
        ClaimId::named("event", "refute-derived-root"),
        "test-refuter",
        Vec::new(),
        Strength::Strict,
        Plane::new(),
    );
    graph.add_evidence(refuter.clone()).unwrap();
    graph.retract(root.evidence.clone(), refuter.id).unwrap();
    assert_eq!(
        graph.evidence_state(&nested.evidence),
        Some(EvidenceState::Unsupported)
    );

    let reordered = "
relation candidate(relation, target)
fact candidate_occ: candidate(relation: &relation_occ, target: &target_occ) @
fact target_occ: object(name: sample) @
fact relation_occ: relation_object(name: observes) @
rule lift strict @: metaedge(relation: ?edge, subject: ?target) <- metaedge(occurrence: ?edge, relation: ?base, subject: ?target), candidate(relation: ?base, target: ?target)
rule construct strict @: metaedge(relation: ?relation, subject: ?target) <- candidate(relation: ?relation, target: ?target)
query metaedge(relation: &relation_occ, subject: &target_occ) @ expect yes
";
    let reordered = evaluate(&agl::parse(reordered).unwrap(), &Plane::new());
    assert_eq!(
        out.metagraph().unwrap().report(),
        reordered.metagraph().unwrap().report()
    );
}

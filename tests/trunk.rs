//! Trunk mechanics: status order decides between strict claims, and `forbid`
//! constraints reject candidates, blaming the least trusted facts.

use agl::eval::ConflictKind;

const BALANCE: &str = "
status measurement > textbook > llm_proposal
fact c1: composition(species: glucose, element: H, n: 12) @ [textbook]
fact c2: composition(species: G6P2, element: H, n: 11) @ [textbook]
fact c3: composition(species: H1, element: H, n: 1) @ [textbook]
fact s1: sign(side: in, value: 1) @ [textbook]
fact s2: sign(side: out, value: -1) @ [textbook]
fact k: checked(element: H) @ [textbook]
fact r1: reaction(id: good) @ [textbook]
fact p1: participates(reaction: good, species: glucose, side: in, coeff: 1) @ [textbook]
fact p2: participates(reaction: good, species: G6P2, side: out, coeff: 1) @ [textbook]
fact p3: participates(reaction: good, species: H1, side: out, coeff: 1) @ [textbook]
fact r2: reaction(id: bad) @ [llm_proposal]
fact q1: participates(reaction: bad, species: glucose, side: in, coeff: 1) @ [llm_proposal]
fact q2: participates(reaction: bad, species: G6P2, side: out, coeff: 1) @ [llm_proposal]
rule net strict @: net(reaction: ?r, element: ?e, value: ?v) <-
    reaction(id: ?r), checked(element: ?e),
    ?v = sum(?s * ?c * ?n) over (participates(reaction: ?r, species: ?sp, side: ?side, coeff: ?c),
                                 sign(side: ?side, value: ?s), composition(species: ?sp, element: ?e, n: ?n))
rule unbal strict @: ¬balanced(reaction: ?r, element: ?e) <- net(reaction: ?r, element: ?e, value: ?v), ?v != 0
forbid ¬balanced(reaction: ?r, element: ?e) @
";

#[test]
fn an_unbalanced_candidate_violates_and_is_blamed() {
    let report = agl::run(&agl::parse(BALANCE).unwrap());
    let v: Vec<_> = report
        .conflicts
        .iter()
        .filter(|c| c.conflict.kind == ConflictKind::Violation)
        .collect();
    assert_eq!(v.len(), 1, "{:?}", report.conflicts);
    assert!(v[0].conflict.positive.contains("reaction: bad"));
    let blame = &v[0].conflict.blame;
    assert!(
        blame.iter().all(|b| b.ends_with("[llm_proposal]")),
        "{blame:?}"
    );
    assert!(blame.iter().any(|b| b.starts_with("q1")), "{blame:?}");
}

#[test]
fn a_less_trusted_strict_claim_loses_instead_of_contradicting() {
    let src = "
status measurement > textbook > llm_proposal
fact t: inert(gas: n2) @ [textbook]
fact l: ¬inert(gas: n2) @ [llm_proposal]
query inert(gas: n2) @ expect yes
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(report.failed_queries().next().is_none());
}

#[test]
fn equal_trust_is_still_a_hard_contradiction() {
    let src = "
status measurement > textbook > llm_proposal
fact t: inert(gas: n2) @ [textbook]
fact u: ¬inert(gas: n2) @ [textbook]
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert_eq!(report.conflicts.len(), 1);
    assert_eq!(report.conflicts[0].conflict.kind, ConflictKind::Hard);
}

#[test]
fn a_contradicting_composition_is_a_uniqueness_conflict_blamed_on_the_candidate() {
    let src = "
status measurement > textbook > llm_proposal
unique composition(n) by (species, element)
fact a: composition(species: ATP4, element: P, n: 3) @ [textbook]
fact b: composition(species: ATP4, element: P, n: 2) @ [llm_proposal]
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert_eq!(report.conflicts.len(), 1);
    assert_eq!(
        report.conflicts[0].conflict.blame,
        vec!["b [llm_proposal]".to_string()]
    );
}

fn glycolysis() -> agl::model::Program {
    agl::parse_file(std::path::Path::new("cases/trunk/glycolysis.agl")).unwrap()
}

#[test]
fn glycolysis_trunk_holds() {
    let report = agl::run(&glycolysis());
    assert!(
        !report.has_errors(),
        "{:?} {:?}",
        report.diags,
        report.errors
    );
    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert_eq!(report.queries.len(), 19);
    assert!(report.failed_queries().next().is_none());
}

#[test]
fn without_the_chebi_is_a_link_the_chain_breaks_at_glucose_6_phosphate() {
    let mut prog = glycolysis();
    prog.facts.retain(|f| f.atom.rel != "is_a");
    let report = agl::run(&prog);
    let v: Vec<&str> = report
        .conflicts
        .iter()
        .filter(|c| c.conflict.kind == ConflictKind::Violation)
        .map(|c| c.conflict.positive.as_str())
        .collect();
    assert_eq!(
        v,
        vec!["forbidden ¬explained(pathway: glycolysis, species: CHEBI_61548)"]
    );
}

#[test]
fn a_wrong_candidate_formula_is_rejected_and_blamed() {
    let mut prog = glycolysis();
    // An LLM proposes two phosphorus atoms for ATP(4-) instead of three.
    let src = "fact llm1: composition(species: CHEBI_30616, element: P, n: 2) @ [llm_proposal]";
    let extra = agl::parse(&format!(
        "status measurement > curated_db > textbook > llm_proposal\n{src}\n"
    ))
    .unwrap();
    prog.facts.extend(extra.facts);
    let report = agl::run(&prog);
    assert!(!report.conflicts.is_empty());
    for c in &report.conflicts {
        assert!(
            c.conflict.blame.iter().any(|b| b == "llm1 [llm_proposal]"),
            "{} blames {:?}",
            c.conflict.positive,
            c.conflict.blame
        );
    }
    assert!(
        report
            .conflicts
            .iter()
            .any(|c| c.conflict.kind == ConflictKind::Uniqueness)
    );
    assert!(
        report
            .conflicts
            .iter()
            .any(|c| c.conflict.positive.contains("¬balanced"))
    );
}

#[test]
fn the_trunk_build_is_reproducible_from_raw_data() {
    let built = std::fs::read_to_string("data/metabolism.agl").unwrap();
    assert!(built.starts_with("# GENERATED by tools/trunk.py build"));
    let manifest = std::fs::read_to_string("data/raw/MANIFEST").unwrap();
    let files = walk(std::path::Path::new("data/raw"));
    assert_eq!(
        manifest.lines().count(),
        files - 1,
        "MANIFEST lists every raw file but itself"
    );
}

fn walk(dir: &std::path::Path) -> usize {
    std::fs::read_dir(dir)
        .unwrap()
        .map(|e| {
            let p = e.unwrap().path();
            if p.is_dir() { walk(&p) } else { 1 }
        })
        .sum()
}

#[test]
fn metabolism_and_oxygen_physiology_answer_together() {
    let prog = agl::parse_file(std::path::Path::new("cases/trunk/oxygen.agl")).unwrap();
    let report = agl::run(&prog);
    assert!(
        !report.has_errors(),
        "{:?} {:?}",
        report.diags,
        report.errors
    );
    assert!(report.conflicts.is_empty(), "{:?}", report.conflicts);
    assert!(report.failed_queries().next().is_none());
    // The junction shows in the grounds: respiration fails for want of oxygen
    // in the anaerobic plane, and the absence itself is a premise.
    let respiring = report
        .queries
        .iter()
        .find(|q| {
            q.query.atom.to_string() == "viable(system: respiring)"
                && q.verdict == agl::model::Verdict::No
        })
        .expect("respiration is not viable without oxygen");
    assert!(
        respiring
            .explanation
            .contains("∅ none in this context: available(species: CHEBI_15379)"),
        "{}",
        respiring.explanation
    );
}

#[test]
fn a_context_is_situated_by_the_program_itself() {
    let src = "
axis oxygen
value oxygen present
value oxygen absent
fact d: delivery(context: c, value: 1.9[L/min]) @
fact n: need(context: c, value: 3[L/min]) @
rule short strict @: situated(context: ?x, axis: oxygen, value: absent) <-
    delivery(context: ?x, value: ?d), need(context: ?x, value: ?m), ?d < ?m
fact o2: available(species: o2) @ oxygen:present
query available(species: o2) @ situate c expect unknown
query available(species: o2) @ oxygen:present expect yes
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(report.failed_queries().next().is_none());
    let q = &report.queries[0];
    assert_eq!(agl::model::plane_to_string(&q.plane), "{oxygen:absent}");
    assert!(
        q.explanation.contains("`c` is situated in {oxygen:absent}"),
        "{}",
        q.explanation
    );
}

#[test]
fn a_context_situated_in_disjoint_planes_is_a_conflict() {
    let src = "
axis oxygen
value oxygen present
value oxygen absent
fact a: situated(context: c, axis: oxygen, value: absent) @
fact b: situated(context: c, axis: oxygen, value: present) @
query anything(x: y) @ situate c expect conflict
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(report.failed_queries().next().is_none());
    assert!(report.queries[0].explanation.contains("disjoint planes"));
}

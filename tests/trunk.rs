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

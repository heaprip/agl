//! Relations between relations (H75, `docs/impl/relations.md`, stage A).
//! Names of gluings and laws ("composition", "associative") are only here.

use agl::bank::Ext;
use agl::layer::{Found, Query, explore, holds, table, to_agl};

/// Every binary relation on `n` points.
fn all(n: usize) -> Vec<Ext> {
    (0..1u32 << (n * n))
        .map(|m| {
            let pairs: Vec<(usize, usize)> = (0..n * n)
                .filter(|b| m >> b & 1 == 1)
                .map(|b| (b / n, b % n))
                .collect();
            Ext::from_pairs(n, &pairs)
        })
        .collect()
}

fn worlds() -> Vec<(usize, Vec<Ext>)> {
    vec![(2, all(2)), (3, all(3))]
}

fn composition() -> Query {
    Query::gluings()
        .into_iter()
        .find(|q| q.to_string() == "{x,y | R(x,a), S(a,y)}")
        .expect("composition is one of the gluings")
}

#[test]
fn gluings_total_by_world_and_laws_by_logic() {
    let found = explore(&worlds());
    // 1. One round of gluing R and S: 60 queries up to logic.
    assert_eq!(found.len(), 60);
    // 2. On worlds of every relation each gluing is everywhere defined.
    assert!(found.iter().all(|f| f.total.iter().all(|t| t.1)));
    // 3. Laws: proposed by the world of 2 points, decided by logic; what
    // logic denies the world of 3 points refutes.
    let laws: Vec<_> = found.iter().flat_map(|f| &f.laws).collect();
    let by_logic = laws.iter().filter(|l| l.logic.is_ok()).count();
    let refuted = laws
        .iter()
        .filter(|l| l.logic.is_err() && l.worlds[1].1 == Some(false))
        .count();
    eprintln!(
        "{} laws, {by_logic} by logic, {refuted} refuted on 3 points",
        laws.len()
    );
    assert_eq!(
        by_logic + refuted,
        laws.len(),
        "a law of the world beyond logic on 3 points"
    );
    // The composition of relations is associative by logic.
    let comp = found.iter().find(|f| f.query == composition()).unwrap();
    let assoc = comp
        .laws
        .iter()
        .find(|l| format!("{} = {}", l.left, l.right) == "(R∘(S∘T)) = ((R∘S)∘T)")
        .expect("associativity is found");
    assert_eq!(assoc.logic, Ok(()));
}

#[test]
fn what_logic_gives_holds_on_three_points() {
    let w = all(3);
    let f: Found = explore(&[(2, all(2))])
        .into_iter()
        .find(|f| f.query == composition())
        .unwrap();
    let t = table(&f.query, &w);
    for l in f.laws.iter().filter(|l| l.logic.is_ok()) {
        assert!(
            holds(&t, w.len(), &l.left, &l.right),
            "{} = {}",
            l.left,
            l.right
        );
    }
}

#[test]
fn a_world_without_every_relation_is_not_total() {
    let some: Vec<Ext> = all(3).into_iter().take(64).collect();
    let found = explore(&[(3, some)]);
    let partial = found.iter().filter(|f| !f.total[0].1).count();
    assert!(partial > 0 && partial < found.len(), "{partial}");
}

#[test]
fn the_kernel_shows_where_a_law_of_small_worlds_fails() {
    let text = to_agl(&explore(&worlds()));
    let prog = agl::parse::parse(&text).unwrap();
    let report = agl::run(&prog);
    assert!(report.diags.is_empty() && report.errors.is_empty());
    assert!(report.conflicts.is_empty());
    let failed: Vec<_> = report
        .failed_queries()
        .map(|q| q.query.atom.to_string())
        .collect();
    assert!(failed.is_empty(), "{failed:?}");
    // Each law seen on 2 points and denied by logic loses on a larger
    // world, and the kernel says so.
    assert!(!report.exceptions.is_empty());
    for e in &report.exceptions {
        assert!(
            e.by.contains("_frozen") || e.by.contains("_not_n"),
            "{}",
            e.by
        );
    }
}

#[test]
fn the_order_of_relations_does_not_matter() {
    let mut w = worlds();
    let a = to_agl(&explore(&w));
    for (_, rels) in &mut w {
        rels.reverse();
    }
    assert_eq!(a, to_agl(&explore(&w)));
}

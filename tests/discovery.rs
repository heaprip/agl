//! The Bombelli step (H53): what the kernel must hold whatever the search.

use agl::eval::evaluate;
use agl::model::Verdict;
use agl::sim::permute;

fn with_all_pairs() -> agl::model::Program {
    let mut src = std::fs::read_to_string("cases/discovery/bombelli.agl").unwrap();
    for a in -10..=10 {
        for b in -10..=10 {
            src.push_str(&format!(
                "fact p{}_{}: pair(re: {a}, im: {b}) @ pairs\n",
                a + 10,
                b + 10
            ));
        }
    }
    agl::parse(&src).unwrap()
}

fn verdicts(prog: &agl::model::Program) -> Vec<(String, Verdict)> {
    agl::run(prog)
        .queries
        .iter()
        .map(|q| (q.query.atom.to_string(), q.verdict))
        .collect()
}

/// Declared before the run: the formula fails without pairs, 4 is a root,
/// the only integer cube roots are 2 ± i, and their sum brings back 4.
#[test]
fn bombelli_finds_two_plus_i_and_returns_to_four() {
    let prog = with_all_pairs();
    assert_eq!(
        verdicts(&prog),
        [
            ("satisfies(eq: bombelli, x: 4)".to_string(), Verdict::Yes),
            (
                "formula_applies(eq: bombelli)".to_string(),
                Verdict::Unknown
            ),
            (
                "cardano_correct(eq: bombelli, x: 4)".to_string(),
                Verdict::Yes
            ),
        ]
    );
    let out = evaluate(&prog, &prog.planes["pairs"]);
    let roots: Vec<String> = out
        .db
        .values()
        .filter(|(a, _)| a.rel == "cube_root")
        .map(|(a, _)| a.to_string())
        .collect();
    assert_eq!(
        roots,
        [
            "cube_root(eq: bombelli, im: -1, re: 2, sign: minus)",
            "cube_root(eq: bombelli, im: 1, re: 2, sign: plus)"
        ]
    );
}

#[test]
fn bombelli_does_not_depend_on_statement_order() {
    let prog = with_all_pairs();
    let sorted = |p: &agl::model::Program| {
        let mut v = verdicts(p);
        v.sort_by(|x, y| x.0.cmp(&y.0));
        v
    };
    let base = sorted(&prog);
    for seed in 0..3 {
        assert_eq!(base, sorted(&permute(&prog, seed)), "permutation {seed}");
    }
}

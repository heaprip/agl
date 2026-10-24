//! Comparison of concepts by definition, checked against the kernel's own
//! evaluation of the same concepts on data. Every run is fixed by its seed;
//! `AGL_SEED=<n>` replays one, `AGL_SIM_SEEDS=<n>` widens the sweep.

use std::collections::BTreeSet;

use agl::model::*;
use agl::sim::{Rng, permute};

fn seeds(default: u64) -> Vec<u64> {
    if let Ok(s) = std::env::var("AGL_SEED") {
        return vec![s.parse().expect("AGL_SEED must be a number")];
    }
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default);
    (0..n).collect()
}

const VARS: [&str; 4] = ["e", "a", "x", "y"];

fn var(v: &str) -> Term {
    Term::Var(v.to_string())
}

/// A random body over `r(s, t)`, `p(u)`, `q(u)` and earlier concepts, with
/// both head variables bound and every inequality over bound variables.
fn gen_body(rng: &mut Rng, earlier: &[String]) -> Vec<Lit> {
    let mut body = Vec::new();
    let mut used: BTreeSet<&str> = BTreeSet::new();
    let n = 1 + rng.below(3);
    for _ in 0..n {
        let (rel, roles): (String, Vec<&str>) =
            match rng.below(if earlier.is_empty() { 3 } else { 4 }) {
                0 | 1 => ("r".into(), vec!["s", "t"]),
                2 => ((if rng.chance(1, 2) { "p" } else { "q" }).into(), vec!["u"]),
                _ => (rng.pick(earlier).clone(), vec!["ego", "alter"]),
            };
        let args = roles
            .iter()
            .map(|r| {
                let v = *rng.pick(&VARS);
                used.insert(v);
                (r.to_string(), var(v))
            })
            .collect();
        body.push(Lit::Atom(Atom::new(rel, args, false)));
    }
    if !used.contains("e") || !used.contains("a") {
        let args = vec![("s".to_string(), var("e")), ("t".to_string(), var("a"))];
        body.push(Lit::Atom(Atom::new("r".into(), args, false)));
        used.extend(["e", "a"]);
    }
    if rng.chance(1, 2) {
        let used: Vec<&str> = used.into_iter().collect();
        let (l, r) = (*rng.pick(&used), *rng.pick(&used));
        if l != r {
            body.push(Lit::Cmp(Expr::Term(var(l)), CmpOp::Ne, Expr::Term(var(r))));
        }
    }
    body
}

fn gen_concepts(seed: u64) -> (Program, Vec<String>) {
    let mut rng = Rng::new(seed);
    let mut src = String::new();
    if rng.chance(1, 2) {
        src.push_str("cover p(u) | q(u)\n");
    }
    let mut names: Vec<String> = Vec::new();
    for k in 0..5 {
        let name = format!("k{k}");
        for _ in 0..1 + rng.below(2) {
            let body: Vec<String> = gen_body(&mut rng, &names)
                .iter()
                .map(Lit::to_string)
                .collect();
            src.push_str(&format!(
                "concept {name}(ego: ?e, alter: ?a) @: {}\n",
                body.join(", ")
            ));
        }
        names.push(name);
    }
    let prog = agl::parse(&src).unwrap_or_else(|e| panic!("seed {seed}: {e}\n{src}"));
    (prog, names)
}

/// Random facts over four individuals, each in some alternative of the cover.
fn gen_facts(rng: &mut Rng, cover: bool) -> Vec<Atom> {
    let people = ["i0", "i1", "i2", "i3"];
    let sym = |s: &str| Term::Sym(s.to_string());
    let mut out = Vec::new();
    for a in people {
        for b in people {
            if rng.chance(1, 3) {
                out.push(Atom::new(
                    "r".into(),
                    vec![("s".into(), sym(a)), ("t".into(), sym(b))],
                    false,
                ));
            }
        }
        let (p, q) = (rng.chance(1, 2), rng.chance(1, 2));
        let (p, q) = if cover && !p && !q {
            (true, false)
        } else {
            (p, q)
        };
        for (rel, on) in [("p", p), ("q", q)] {
            if on {
                out.push(Atom::new(rel.into(), vec![("u".into(), sym(a))], false));
            }
        }
    }
    out
}

/// The answers of `rel` that the kernel derives from `facts`.
fn answers(prog: &Program, facts: &[Atom], rel: &str) -> BTreeSet<String> {
    let mut p = prog.clone();
    p.facts = facts
        .iter()
        .enumerate()
        .map(|(i, a)| Fact {
            id: format!("d{i}"),
            atom: a.clone(),
            plane: Plane::new(),
            status: "given".into(),
            line: 0,
        })
        .collect();
    let out = agl::eval::evaluate(&p, &Plane::new());
    out.db
        .values()
        .filter(|(a, _)| a.rel == rel && !a.neg)
        .map(|(a, _)| {
            let mut args = a.args.clone();
            args.sort_by(|x, y| x.0.cmp(&y.0));
            format!("{args:?}")
        })
        .collect()
}

fn head_key(head: &[(String, Term)]) -> String {
    let mut args = head.to_vec();
    args.sort_by(|a, b| a.0.cmp(&b.0));
    format!("{args:?}")
}

#[test]
fn comparison_by_definition_agrees_with_evaluation_on_data() {
    let root = Plane::new();
    let (mut below, mut not_below, mut skipped) = (0, 0, 0);
    for seed in seeds(150) {
        let (prog, names) = gen_concepts(seed);
        let cover = !prog.covers.is_empty();
        let mut rng = Rng::new(seed ^ 0xA5A5);
        let data: Vec<Vec<Atom>> = (0..20).map(|_| gen_facts(&mut rng, cover)).collect();
        for a in &names {
            for b in &names {
                let w = match agl::concept::witness(&prog, a, &root, b, &root) {
                    Ok(w) => w,
                    Err(e) if e.contains("too many") => {
                        skipped += 1;
                        continue;
                    }
                    Err(e) => panic!("seed {seed}: {e}"),
                };
                match w {
                    None => {
                        below += 1;
                        for facts in &data {
                            let (xa, xb) = (answers(&prog, facts, a), answers(&prog, facts, b));
                            assert!(
                                xa.is_subset(&xb),
                                "seed {seed}: {a} ⊑ {b} by definition, but not on {facts:?}"
                            );
                        }
                    }
                    Some((facts, head)) => {
                        not_below += 1;
                        let key = head_key(&head);
                        assert!(
                            answers(&prog, &facts, a).contains(&key),
                            "seed {seed}: witness for {a} ⋢ {b} lacks {a}: {facts:?}"
                        );
                        assert!(
                            !answers(&prog, &facts, b).contains(&key),
                            "seed {seed}: witness for {a} ⋢ {b} has {b}: {facts:?}"
                        );
                    }
                }
            }
        }
    }
    assert!(
        below > 0 && not_below > 5 * skipped,
        "{below} below, {not_below} not, {skipped} too large"
    );
}

#[test]
fn kinship_does_not_depend_on_statement_order() {
    let src = std::fs::read_to_string("cases/kinship.agl").unwrap();
    let prog = agl::parse(&src).unwrap();
    let base = (agl::render(&agl::run(&prog)), agl::concept::report(&prog));
    for k in 0..3 {
        let p = permute(&prog, 7 + k);
        let other = (agl::render(&agl::run(&p)), agl::concept::report(&p));
        assert_eq!(base.0, other.0, "permutation {k}: report differs");
        assert_eq!(base.1, other.1, "permutation {k}: concept report differs");
    }
}

#[test]
fn a_concept_defined_through_itself_is_an_error() {
    let src = "
concept a(ego: ?e, alter: ?x) @: b(ego: ?e, alter: ?x)
concept b(ego: ?e, alter: ?x) @: a(ego: ?e, alter: ?x)
compare a @ vs b @
";
    let report = agl::run(&agl::parse(src).unwrap());
    assert!(report.has_errors());
    let err = report.compares[0].verdict.clone().unwrap_err();
    assert!(err.contains("defined through itself"), "{err}");
}

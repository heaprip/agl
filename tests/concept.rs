//! Comparison of concepts by definition, checked against the kernel's own
//! evaluation of the same concepts on data. Every run is fixed by its seed;
//! `AGL_SEED=<n>` replays one, `AGL_SIM_SEEDS=<n>` widens the sweep.

use std::collections::{BTreeMap, BTreeSet};

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
                ((*r).into(), var(v))
            })
            .collect();
        body.push(Lit::Atom(Atom::new(rel.into(), args, false)));
    }
    if !used.contains("e") || !used.contains("a") {
        let args = vec![("s".into(), var("e")), ("t".into(), var("a"))];
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
    let sym = |s: &str| Term::Sym(s.into());
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

/// The answers of every relation that the kernel derives from `facts`.
fn answers(prog: &Program, facts: &[Atom]) -> BTreeMap<String, BTreeSet<String>> {
    let mut p = prog.clone();
    p.facts = facts
        .iter()
        .enumerate()
        .map(|(i, a)| Fact {
            id: format!("d{i}").into(),
            atom: a.clone(),
            plane: Plane::new(),
            status: "given".into(),
            line: 0,
        })
        .collect();
    let out = agl::eval::evaluate(&p, &Plane::new());
    let mut by_rel: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (a, _) in out.db.values().filter(|(a, _)| !a.neg) {
        let mut args = a.args.clone();
        args.sort_by(|x, y| x.0.cmp(&y.0));
        by_rel
            .entry(a.rel.to_string())
            .or_default()
            .insert(format!("{args:?}"));
    }
    by_rel
}

fn of<'a>(answers: &'a BTreeMap<String, BTreeSet<String>>, rel: &str) -> &'a BTreeSet<String> {
    static EMPTY: BTreeSet<String> = BTreeSet::new();
    answers.get(rel).unwrap_or(&EMPTY)
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
        let on_data: Vec<_> = data.iter().map(|facts| answers(&prog, facts)).collect();
        let mut forms = Vec::new();
        for a in &names {
            forms.push(agl::concept::normal_form(&prog, a, &root));
        }
        for (a, fa) in names.iter().zip(&forms) {
            for (b, fb) in names.iter().zip(&forms) {
                let w = match (fa, fb) {
                    (Ok(ua), Ok(ub)) => agl::concept::witness_of(&prog, ua, &root, ub, &root),
                    (Err(e), _) | (_, Err(e)) => Err(e.clone()),
                };
                let w = match w {
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
                        for (facts, ans) in data.iter().zip(&on_data) {
                            assert!(
                                of(ans, a).is_subset(of(ans, b)),
                                "seed {seed}: {a} ⊑ {b} by definition, but not on {facts:?}"
                            );
                        }
                    }
                    Some((facts, head)) => {
                        not_below += 1;
                        let key = head_key(&head);
                        let ans = answers(&prog, &facts);
                        assert!(
                            of(&ans, a).contains(&key),
                            "seed {seed}: witness for {a} ⋢ {b} lacks {a}: {facts:?}"
                        );
                        assert!(
                            !of(&ans, b).contains(&key),
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

fn compared(src: &str) -> Vec<String> {
    agl::run(&agl::parse(src).unwrap())
        .compares
        .iter()
        .map(|c| match &c.verdict {
            Ok(r) => r.to_string(),
            Err(e) => e.clone(),
        })
        .collect()
}

#[test]
fn a_role_named_like_a_numbered_variable_does_not_merge_variables() {
    let src = "
relation edge(from, to)
concept a(x1: ?a) @: edge(from: ?a, to: ?b)
concept loop(x1: ?a) @: edge(from: ?a, to: ?a)
compare a @ vs loop @
";
    assert_eq!(compared(src), ["above"]);
}

#[test]
fn worlds_name_the_constants_of_the_rules() {
    let src = "
relation parenthood(child, parent)
concept parent(ego: ?e, alter: ?a) @: parenthood(child: ?e, parent: ?a)
rule rb strict @: b(ego: ?e, alter: ?a) <- parenthood(child: ?e, parent: ?a), ?a != adam
compare parent @ vs b @
";
    assert_eq!(compared(src), ["not_below"]);
}

#[test]
fn against_rules_that_are_not_monotone_below_is_not_claimed() {
    let src = "
relation parenthood(child, parent)
concept parent(ego: ?e, alter: ?a) @: parenthood(child: ?e, parent: ?a)
rule rb strict @: b(ego: ?e, alter: ?a) <- parenthood(child: ?e, parent: ?a), ?n = count(?c) over (parenthood(child: ?c, parent: ?a)), ?n < 2
compare parent @ vs b @
";
    assert_eq!(compared(src), ["unknown"]);
}

#[test]
fn many_variables_keep_the_canonical_form_independent_of_atom_order() {
    let atoms = [
        "r(s: ?e, t: ?b1)",
        "r(s: ?b1, t: ?b2)",
        "r(s: ?b2, t: ?b3)",
        "r(s: ?b3, t: ?b4)",
        "r(s: ?b4, t: ?b5)",
        "r(s: ?b5, t: ?b6)",
        "r(s: ?b6, t: ?b7)",
        "r(s: ?b1, t: ?b8)",
    ];
    let report = |body: &[&str]| {
        let src = format!(
            "relation r(s, t)\nconcept big(ego: ?e) @: {}\n",
            body.join(", ")
        );
        agl::concept::report(&agl::parse(&src).unwrap())
    };
    let mut reversed = atoms;
    reversed.reverse();
    assert_eq!(report(&atoms), report(&reversed));
}

//! `nesting` against the two rules it stands for (H61, step 2a): the report
//! and every closure must be the same, byte for byte.
//! `AGL_SIM_SEEDS=<n>` widens the sweep, `AGL_SEED=<n>` replays one seed.

use agl::eval::evaluate;
use agl::model::Plane;
use agl::sim::Rng;

fn seeds() -> Vec<u64> {
    if let Ok(s) = std::env::var("AGL_SEED") {
        return vec![s.parse().expect("AGL_SEED must be a number")];
    }
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);
    (0..n).collect()
}

const RULES: &str = "rule nt_base strict @: n(a: ?x, b: ?y) <- e(x: ?x, y: ?y)\n\
                     rule nt_step strict @: n(a: ?x, b: ?y) <- e(x: ?x, y: ?z), n(a: ?z, b: ?y)";
const NESTING: &str = "nesting nt: n(a, b) by e(x, y)\n";

/// Every closure, as text: atoms with their derivations, conflicts, errors.
fn closures(src: &str) -> String {
    let prog = agl::parse(src).expect("parse");
    let mut planes: Vec<Plane> = vec![Plane::new()];
    planes.extend(prog.planes.values().cloned());
    let mut s = String::new();
    for p in planes {
        let out = evaluate(&prog, &p);
        for (k, (_, ds)) in &out.db {
            let mut ds: Vec<String> = ds
                .iter()
                .map(|d| format!("{} {} {} {:?}", d.source, d.strict, d.rank, d.premises))
                .collect();
            ds.sort();
            s += &format!("{k}: {ds:?}\n");
        }
        s += &format!(
            "{:?}\n{:?}\n{:?}\n",
            out.conflicts.keys(),
            out.defeated,
            out.errors
        );
    }
    s
}

fn same(rules: &str, nesting: &str, what: &str) {
    assert_eq!(
        agl::render(&agl::run(&agl::parse(rules).expect("parse"))),
        agl::render(&agl::run(&agl::parse(nesting).expect("parse"))),
        "{what}: reports differ"
    );
    assert_eq!(
        closures(rules),
        closures(nesting),
        "{what}: closures differ"
    );
}

/// A random program over an edge relation `e` and its closure `n`: edges as
/// facts in planes and with statuses, edges against them, edges from other
/// rules (some through `n` itself), `n` given directly, rules and queries
/// that read `n`.
fn program(seed: u64, closure: &str) -> String {
    let mut rng = Rng::new(seed);
    let k = 2 + rng.below(7);
    let node = |rng: &mut Rng| format!("v{}", rng.below(k));
    let mut s = String::from(
        "status hi > mid > lo\naxis w\nvalue w p\nvalue w q\nplane pp = w:p\nplane qq = w:q\n",
    );
    s += closure;
    s += "\n";
    let planes = ["@", "@ w:p", "@ w:q"];
    let statuses = ["hi", "mid", "lo"];
    for i in 0..rng.below(14) {
        let (a, b) = (node(&mut rng), node(&mut rng));
        let neg = if rng.chance(1, 8) { "¬" } else { "" };
        let plane = rng.pick(&planes);
        let status = rng.pick(&statuses);
        s += &format!("fact e{i}: {neg}e(x: {a}, y: {b}) {plane} [{status}]\n");
    }
    for i in 0..rng.below(3) {
        let (a, b) = (node(&mut rng), node(&mut rng));
        let neg = if rng.chance(1, 4) { "¬" } else { "" };
        let extra = if rng.chance(1, 3) { ", via: w1" } else { "" };
        let status = rng.pick(&statuses);
        s += &format!("fact g{i}: {neg}n(a: {a}, b: {b}{extra}) @ [{status}]\n");
    }
    for i in 0..rng.below(4) {
        let (a, b) = (node(&mut rng), node(&mut rng));
        s += &format!("fact f{i}: f(x: {a}, y: {b}) @ [lo]\n");
    }
    if rng.chance(1, 2) {
        s += "rule fe defeasible @: e(x: ?a, y: ?b) <- f(x: ?a, y: ?b)\n";
    }
    if rng.chance(1, 3) {
        s += "rule fn defeasible @ w:q: ¬e(x: ?a, y: ?b) <- f(x: ?b, y: ?a)\n";
    }
    if rng.chance(1, 3) {
        // Edges that depend on the closure: the label pass must repeat.
        let v = node(&mut rng);
        s += &format!(
            "rule back defeasible @: e(x: {v}, y: ?b) <- n(a: ?b, b: {v}), f(x: ?b, y: ?c)\n"
        );
    }
    let v = node(&mut rng);
    s += &format!("rule up strict @: top(x: ?a) <- n(a: ?a, b: {v})\n");
    if rng.chance(1, 3) {
        s += "rule self strict @: loop(x: ?a) <- n(a: ?a, b: ?a)\nforbid loop(x: ?a) @\n";
    }
    for _ in 0..3 {
        let (a, b) = (node(&mut rng), node(&mut rng));
        let plane = rng.pick(&["pp", "qq", ""]);
        s += &format!("query n(a: {a}, b: {b}) @ {plane}\n");
    }
    s
}

#[test]
fn nesting_equals_its_rules_on_random_programs() {
    for seed in seeds() {
        same(
            &program(seed, RULES),
            &program(seed, NESTING),
            &format!("seed {seed}"),
        );
    }
}

#[test]
fn nesting_equals_its_rules_on_kinship() {
    let src = std::fs::read_to_string("cases/kinship.agl").unwrap();
    let anc1 =
        "rule anc1 strict @: ancestor(ego: ?e, alter: ?a) <- parenthood(child: ?e, parent: ?a)\n";
    let anc2 = "rule anc2 strict @: ancestor(ego: ?e, alter: ?a) <- parenthood(child: ?e, parent: ?p), ancestor(ego: ?p, alter: ?a)\n";
    assert!(src.contains(anc1) && src.contains(anc2));
    let rules = src
        .replace(anc1, "rule anc_base strict @: ancestor(ego: ?x, alter: ?y) <- parenthood(child: ?x, parent: ?y)\n")
        .replace(anc2, "rule anc_step strict @: ancestor(ego: ?x, alter: ?y) <- parenthood(child: ?x, parent: ?z), ancestor(ego: ?z, alter: ?y)\n");
    let nesting = src
        .replace(
            anc1,
            "nesting anc: ancestor(ego, alter) by parenthood(child, parent)\n",
        )
        .replace(anc2, "\n");
    same(&rules, &nesting, "kinship");
}

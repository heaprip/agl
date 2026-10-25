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
                .map(|d| {
                    let ps: Vec<&str> = out.db.premise_keys(d).collect();
                    format!("{} {} {} {:?}", d.source, d.strict, d.rank, ps)
                })
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

/// A program where only rule bodies read `n` (step 2b): no queries, forbids
/// or denials of `n`. Edges are facts, except on some seeds, where a rule
/// derives them and the nesting must fall back to being whole.
fn lazy_program(seed: u64, closure: &str) -> String {
    let mut rng = Rng::new(seed);
    let k = 2 + rng.below(9);
    let node = |rng: &mut Rng| format!("v{}", rng.below(k));
    let mut s = String::from(
        "status hi > mid > lo\naxis w\nvalue w p\nvalue w q\nplane pp = w:p\nplane qq = w:q\n",
    );
    s += closure;
    s += "\n";
    let planes = ["@", "@ w:p", "@ w:q"];
    let statuses = ["hi", "mid", "lo"];
    for i in 0..rng.below(16) {
        let (a, b) = (node(&mut rng), node(&mut rng));
        let neg = if rng.chance(1, 8) { "¬" } else { "" };
        let plane = rng.pick(&planes);
        let status = rng.pick(&statuses);
        s += &format!("fact e{i}: {neg}e(x: {a}, y: {b}) {plane} [{status}]\n");
    }
    for i in 0..rng.below(3) {
        let (a, b) = (node(&mut rng), node(&mut rng));
        let extra = if rng.chance(1, 3) { ", via: w1" } else { "" };
        s += &format!("fact g{i}: n(a: {a}, b: {b}{extra}) @ [mid]\n");
    }
    if rng.chance(1, 4) {
        s += "fact f0: f(x: v0, y: v1) @ [lo]\nrule fe defeasible @: e(x: ?a, y: ?b) <- f(x: ?a, y: ?b)\n";
    }
    let (v, w) = (node(&mut rng), node(&mut rng));
    s += &format!("rule up strict @: top(x: ?a) <- n(a: ?a, b: {v})\n");
    s += &format!("rule down defeasible @ w:p: low(x: ?b) <- n(a: {w}, b: ?b)\n");
    s += &format!("rule both strict @: pair(x: ?a) <- n(a: ?a, b: {v}), n(a: {w}, b: ?a)\n");
    if rng.chance(1, 2) {
        s += "rule self strict @: loop(x: ?a) <- n(a: ?a, b: ?a)\nforbid loop(x: ?a) @\n";
    }
    if rng.chance(1, 3) {
        s += "rule via strict @: routed(x: ?a) <- n(a: ?a, b: ?b, via: w1)\n";
    }
    if rng.chance(1, 4) {
        s += "rule all strict @: linked(x: ?a, y: ?b) <- n(a: ?a, b: ?b)\n";
    }
    for _ in 0..3 {
        let a = node(&mut rng);
        let plane = rng.pick(&["pp", "qq", ""]);
        s += &format!("query top(x: {a}) @ {plane}\nquery pair(x: {a}) @ {plane}\n");
    }
    s
}

/// Closures of the lazy program: every atom made equals the whole version's,
/// and every atom other than `n` is the same in both. Returns the atoms of
/// `n` derived, lazy and whole.
fn lazy_matches_whole(lazy: &str, whole: &str, what: &str) -> (usize, usize) {
    let (pl, pw) = (agl::parse(lazy).unwrap(), agl::parse(whole).unwrap());
    let mut planes: Vec<Plane> = vec![Plane::new()];
    planes.extend(pw.planes.values().cloned());
    let (mut made, mut all) = (0, 0);
    for p in planes {
        let (ol, ow) = (evaluate(&pl, &p), evaluate(&pw, &p));
        let show = |db: &agl::eval::Db, ds: &Vec<agl::eval::Derivation>| {
            let mut v: Vec<String> = ds
                .iter()
                .map(|d| {
                    let ps: Vec<&str> = db.premise_keys(d).collect();
                    format!("{} {} {} {:?}", d.source, d.strict, d.rank, ps)
                })
                .collect();
            v.sort();
            v
        };
        for (k, (a, ds)) in &ow.db {
            match ol.db.get(k) {
                // A given atom of `n` no rule asked for keeps only its fact.
                Some((_, dl)) if a.rel == "n" && dl.iter().all(|d| d.is_fact) => {}
                Some((_, dl)) => {
                    assert_eq!(show(&ol.db, dl), show(&ow.db, ds), "{what}: {k} in {p:?}")
                }
                None => assert_eq!(a.rel, "n", "{what}: {k} missing in {p:?}"),
            }
        }
        assert!(
            ol.db.keys().all(|k| ow.db.contains_key(k)),
            "{what}: extra atom in {p:?}"
        );
        assert_eq!(
            ol.conflicts.keys().collect::<Vec<_>>(),
            ow.conflicts.keys().collect::<Vec<_>>(),
            "{what}"
        );
        assert_eq!(ol.errors, ow.errors, "{what}");
        made += ol
            .db
            .values()
            .filter(|(a, ds)| a.rel == "n" && ds.iter().any(|d| !d.is_fact))
            .count();
        all += ow.db.values().filter(|(a, _)| a.rel == "n").count();
    }
    (made, all)
}

#[test]
fn lazy_nesting_equals_whole_where_only_rules_read_it() {
    let (mut made, mut all, mut runs) = (0, 0, 0);
    for seed in seeds() {
        let lazy = lazy_program(seed, "nesting nt: n(a, b) by e(x, y) lazy\n");
        let whole = lazy_program(seed, NESTING);
        assert_eq!(
            agl::render(&agl::run(&agl::parse(&lazy).unwrap())),
            agl::render(&agl::run(&agl::parse(&whole).unwrap())),
            "seed {seed}: reports differ"
        );
        let (m, a) = lazy_matches_whole(&lazy, &whole, &format!("seed {seed}"));
        made += m;
        all += a;
        runs += 1;
    }
    eprintln!("lazy: {made} atoms of n made against {all} whole, {runs} programs");
    assert!(made < all, "laziness never saved an atom");
}

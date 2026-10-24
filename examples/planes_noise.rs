//! Experiment for H52: what goes with what when planes are many.
//!
//! N planes (values of one axis), K individuals in each, two attributes `a`
//! and `b` that are independent coin flips. In a planted share of the planes
//! `a → b` is made to hold: every individual with `a` gets `b`. The question
//! is which planes show "here a → b holds" — the naive answer (no exception in
//! the plane) and the answer after Benjamini–Hochberg at q = 0.1, with the
//! p-value of a plane taken as p0^n: the chance that n individuals with `a`
//! all have `b` when `b` follows `a` only as often as overall (p0).
//!
//!     cargo run --release --example planes_noise -- N K [seed]
//!
//! The output is deterministic; time it from outside.

use agl::sim::Rng;

const PLANTED_PERCENT: usize = 5;
const Q: f64 = 0.1;

fn main() {
    let args: Vec<usize> = std::env::args()
        .skip(1)
        .map(|s| s.parse().expect("numbers: N K [seed]"))
        .collect();
    let (n, k) = (args[0], args[1]);
    let seed = args.get(2).copied().unwrap_or(1) as u64;
    let mut rng = Rng::new(seed);
    let mut src = String::from("axis group\nrelation a(id)\nrelation b(id)\n");
    let mut planted = std::collections::BTreeSet::new();
    for g in 0..n {
        src.push_str(&format!("value group g{g}\n"));
        if rng.below(100) < PLANTED_PERCENT {
            planted.insert(format!("{{group:g{g}}}"));
        }
    }
    for g in 0..n {
        let plant = planted.contains(&format!("{{group:g{g}}}"));
        for i in 0..k {
            let a = rng.below(2) == 1;
            let b = rng.below(2) == 1 || (plant && a);
            for (rel, on) in [("a", a), ("b", b)] {
                if on {
                    src.push_str(&format!(
                        "fact {rel}_{g}_{i}: {rel}(id: p{g}_{i}) @ group:g{g}\n"
                    ));
                }
            }
        }
    }
    let prog = agl::parse(&src).expect("generated program parses");
    let (table, complete) = agl::extent::table(&prog);
    let rels = &table["id"];
    let empty = Default::default();
    let (with_a, with_b) = (&rels["a"], rels.get("b").unwrap_or(&empty));
    // Per plane: individuals with `a`, and those of them without `b`.
    let mut per: std::collections::BTreeMap<&str, (usize, usize)> = Default::default();
    for (ctx, obj) in with_a {
        let e = per.entry(ctx).or_default();
        e.0 += 1;
        if !with_b.contains(&(ctx.clone(), obj.clone())) {
            e.1 += 1;
        }
    }
    let total_a: usize = per.values().map(|x| x.0).sum();
    let total_exc: usize = per.values().map(|x| x.1).sum();
    let p0 = 1.0 - total_exc as f64 / total_a as f64;
    let mut naive = Vec::new();
    let mut tests: Vec<(f64, &str)> = Vec::new();
    for (ctx, (na, exc)) in &per {
        let p = if *exc == 0 { p0.powi(*na as i32) } else { 1.0 };
        if *exc == 0 {
            naive.push(*ctx);
        }
        tests.push((p, ctx));
    }
    tests.sort_by(|x, y| x.0.total_cmp(&y.0).then_with(|| x.1.cmp(y.1)));
    let m = n as f64;
    let cut = tests
        .iter()
        .enumerate()
        .filter(|(i, (p, _))| *p <= (*i as f64 + 1.0) / m * Q)
        .map(|(i, _)| i + 1)
        .max()
        .unwrap_or(0);
    let bh: Vec<&str> = tests[..cut].iter().map(|(_, c)| *c).collect();
    let split = |found: &[&str]| {
        let t = found.iter().filter(|c| planted.contains(**c)).count();
        (t, found.len() - t)
    };
    let (nt, nf) = split(&naive);
    let (bt, bf) = split(&bh);
    println!(
        "N={n} K={k} seed={seed}: planted {}, contexts complete: {complete}, p0 = {p0:.3}",
        planted.len()
    );
    println!("  naive (no exception in the plane): {nt} planted, {nf} by chance");
    println!("  Benjamini–Hochberg q={Q}:           {bt} planted, {bf} by chance");
}

//! Step 2 of the ladder H57: adjoin a root, after Cauchy (1847).
//!
//! The case `cases/discovery/cauchy.agl` knows polynomials a + bX, the
//! distributive law and reduction modulo X² − s, but not the rule for
//! multiplying pairs and not which s to take. The generator reads the
//! anomaly (the formula needs √d with d < 0), proposes s = d/k² for every
//! integer k with k² | d and two controls from Hahn, s = 0 and s = +1, and
//! makes a plane for each. In each plane it adds elements |a|, |b| <= BOUND
//! in an order drawn from the seed, a batch at a time, until the kernel
//! returns to the checked root or the elements run out. Then it checks the
//! laws on pairs drawn from the seed and compares the products the kernel
//! derived with Hamilton's rule, which the case does not contain.
//!
//!     cargo run --release --example cauchy            # seed 1
//!     cargo run --release --example cauchy -- 7       # another seed
//!     AGL_TRACE=1 cargo run --release --example cauchy  # every batch
//!
//! Criterion declared before the run: docs/hypotheses.md, H57, step 2.
//! Nothing is written to disk: the trace is recomputed from the seed.

use std::collections::BTreeMap;

use agl::eval::{Outcome, evaluate};
use agl::model::{Atom, Plane, Term};
use agl::sim::Rng;

const CASE: &str = "cases/discovery/cauchy.agl";
const BOUND: i64 = 11;
const BATCH: usize = 50;
const PROBES: usize = 30;
const REAL_PROBES: usize = 10;

fn name(a: i64, b: i64) -> String {
    let n = |x: i64| {
        if x < 0 {
            format!("m{}", -x)
        } else {
            x.to_string()
        }
    };
    format!("e_{}_{}", n(a), n(b))
}

fn element(a: i64, b: i64) -> String {
    let p = name(a, b);
    format!(
        "fact {p}_0: coef(p: {p}, deg: 0, c: {a}) @\nfact {p}_1: coef(p: {p}, deg: 1, c: {b}) @\n"
    )
}

fn plane_name(s: i64) -> String {
    if s < 0 {
        format!("adj_m{}", -s)
    } else {
        format!("adj_{s}")
    }
}

fn plane_decl(s: i64) -> String {
    let p = plane_name(s);
    format!("value repr {p}\nplane {p} = repr:{p}\nfact {p}: adjoined(s: {s}) @ {p}\n")
}

fn num(a: &Atom, role: &str) -> Option<f64> {
    a.args.iter().find_map(|(r, t)| match t {
        Term::Num(x, _) if r == role => Some(*x),
        _ => None,
    })
}

fn sym<'a>(a: &'a Atom, role: &str) -> Option<&'a str> {
    a.args.iter().find_map(|(r, t)| match t {
        Term::Sym(x) if r == role => Some(x.as_str()),
        _ => None,
    })
}

fn derived<'a>(out: &'a Outcome, rel: &'a str) -> impl Iterator<Item = &'a Atom> + 'a {
    out.db
        .values()
        .map(|(a, _)| a)
        .filter(move |a| a.rel == rel && !a.neg)
}

fn main() {
    let seed: u64 = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("seed"))
        .unwrap_or(1);
    let trace = std::env::var("AGL_TRACE").is_ok();
    let src = std::fs::read_to_string(CASE).unwrap();
    let base = agl::parse(&src).unwrap();
    let mut rng = Rng::new(seed);

    // 1. The anomaly and the radicand it stops at.
    let report = agl::run(&base);
    let failed: Vec<_> = report
        .failed_queries()
        .map(|q| q.query.atom.to_string())
        .collect();
    let root = evaluate(&base, &Plane::new());
    assert!(!root.truncated, "closure truncated: raise the batch split");
    let d = derived(&root, "radicand")
        .find_map(|a| num(a, "value"))
        .expect("radicand");
    println!("anomaly: {failed:?}; radicand d = {d}");

    // 2. Candidates: s = d/k² for integer k with k² | d, and Hahn's controls.
    let d = d as i64;
    let mut cands: Vec<i64> = (1..=d.abs())
        .take_while(|k| k * k <= d.abs())
        .filter(|k| d % (k * k) == 0)
        .map(|k| d / (k * k))
        .chain([0, 1])
        .collect();
    rng.shuffle(&mut cands);
    println!("candidates s (X² = s), in seed order: {cands:?}");

    let mut elems: Vec<(i64, i64)> = (-BOUND..=BOUND)
        .flat_map(|a| (-BOUND..=BOUND).map(move |b| (a, b)))
        .collect();
    rng.shuffle(&mut elems);
    let reals: Vec<(i64, i64)> = elems.iter().copied().filter(|e| e.1 == 0).collect();
    let mut probes: Vec<((i64, i64), (i64, i64))> = Vec::new();
    for _ in 0..PROBES {
        probes.push((*rng.pick(&elems), *rng.pick(&elems)));
    }
    for _ in 0..REAL_PROBES {
        probes.push((*rng.pick(&reals), *rng.pick(&reals)));
    }
    let coords: BTreeMap<String, (i64, i64)> =
        elems.iter().map(|&(a, b)| (name(a, b), (a, b))).collect();

    // 3. Search in each plane; 4. laws and the derived product.
    let mut passed = Vec::new();
    for &s in &cands {
        let pn = plane_name(s);
        let mut text = src.clone() + &plane_decl(s);
        let mut sqrt = None;
        let mut answer = None;
        for (k, batch) in elems.chunks(BATCH).enumerate() {
            for &(a, b) in batch {
                text.push_str(&element(a, b));
            }
            let prog = agl::parse(&text).unwrap();
            let out = evaluate(&prog, &prog.planes[&pn]);
            assert!(!out.truncated, "closure truncated: raise the batch split");
            let tried = ((k + 1) * BATCH).min(elems.len());
            let roots: Vec<String> = derived(&out, "cube_root").map(|a| a.to_string()).collect();
            if sqrt.is_none() && derived(&out, "sqrt_of").next().is_some() {
                sqrt = Some(tried);
            }
            if trace {
                println!(
                    "  {pn} batch {}: {tried} elements, cube roots: {roots:?}",
                    k + 1
                );
            }
            if derived(&out, "cardano_correct").next().is_some() {
                answer = Some((tried, roots));
                break;
            }
        }

        for (x, y) in &probes {
            for (l, r) in [(x, y), (y, x)] {
                text.push_str(&format!(
                    "fact pr_{}_{}: probe(l: {}, r: {}) @\n",
                    name(l.0, l.1),
                    name(r.0, r.1),
                    name(l.0, l.1),
                    name(r.0, r.1)
                ));
            }
        }
        for &(a, b) in &elems {
            if !text.contains(&format!("fact {}_0:", name(a, b))) {
                text.push_str(&element(a, b));
            }
        }
        // Repeated probes repeat fact names; keep the first.
        let mut seen = std::collections::BTreeSet::new();
        let text: String = text
            .lines()
            .filter(|l| !l.starts_with("fact pr_") || seen.insert(l.to_string()))
            .map(|l| format!("{l}\n"))
            .collect();
        let prog = agl::parse(&text).unwrap();
        let out = evaluate(&prog, &prog.planes[&pn]);
        assert!(!out.truncated, "closure truncated: raise the batch split");
        let broken: Vec<String> = derived(&out, "law_broken").map(|a| a.to_string()).collect();
        let mut products: BTreeMap<(String, String), [f64; 2]> = BTreeMap::new();
        for a in derived(&out, "reduced").filter(|a| sym(a, "kind") == Some("product")) {
            let key = (sym(a, "l").unwrap().into(), sym(a, "r").unwrap().into());
            products.entry(key).or_default()[num(a, "deg").unwrap() as usize] =
                num(a, "c").unwrap();
        }
        let hamilton = products
            .iter()
            .filter(|((l, r), p)| {
                let ((a, b), (c, e)) = (coords[l], coords[r]);
                **p == [(a * c - b * e) as f64, (a * e + b * c) as f64]
            })
            .count();

        println!("plane {pn} (X² = {s}):");
        match sqrt {
            Some(n) => println!("  (1) √{d} found after {n} elements"),
            None => println!("  (1) no √{d} among {} elements", elems.len()),
        }
        match &answer {
            Some((n, roots)) => {
                println!("  (2) back to the root 4 after {n} elements; cube roots: {roots:?}");
                passed.push(s);
            }
            None => println!("  (2) not answered"),
        }
        println!(
            "  (3) laws on {} ordered probes: broken {broken:?}",
            products.len()
        );
        println!(
            "  products equal to Hamilton's (ac − bd, ad + bc): {hamilton} of {}",
            products.len()
        );
    }
    println!("passed the sieve: {passed:?}");
}

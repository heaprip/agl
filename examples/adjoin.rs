//! Step 3 of the ladder H57: one way of adjoining a root for every equation
//! that does not solve in the old domain.
//!
//! The problem file gives only an equation and the old domain; the rules
//! are `cases/lib/adjoin.agl`. The generator names the old elements (b = 0),
//! asks the kernel whether the equation solves, and on the anomaly makes a
//! plane where exactly that equation is adjoined: X with L(X) = R(X). There
//! it names elements a + bX, multipliers u for the congruence and probe
//! pairs drawn from the seed, and reports the sieve: solved, conservative,
//! no zero divisors.
//!
//!     cargo run --release --example adjoin -- cases/discovery/adjoin/negatives.agl [SEED]
//!     cargo run --release --example adjoin -- cases/discovery/adjoin/square_four.agl 1 force
//!
//! `force` adjoins the equation even without an anomaly: a control for the
//! sieve, since the generator itself adjoins only what failed.
//!
//! Criterion declared before the run: docs/hypotheses.md, H57, step 3.

use std::collections::BTreeMap;
use std::path::Path;

use agl::eval::{Outcome, evaluate};
use agl::model::{Atom, Plane, Term};
use agl::sim::Rng;

/// Multipliers u = k0 + k1 X with |ki| <= K.
const K: i64 = 5;
const PROBES: usize = 2000;

fn name(prefix: &str, a: i64, b: i64) -> String {
    let n = |x: i64| {
        if x < 0 {
            format!("m{}", -x)
        } else {
            x.to_string()
        }
    };
    format!("{prefix}_{}_{}", n(a), n(b))
}

fn poly(rel: &str, prefix: &str, a: i64, b: i64) -> String {
    let p = name(prefix, a, b);
    format!(
        "fact {p}_0: {rel}({}: {p}, deg: 0, c: {a}) @\nfact {p}_1: {rel}({}: {p}, deg: 1, c: {b}) @\n",
        if rel == "mult" { "u" } else { "p" },
        if rel == "mult" { "u" } else { "p" },
    )
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

/// The sieve in one context: solutions and broken laws by law.
pub fn sieve(out: &Outcome) -> (Vec<String>, BTreeMap<String, Vec<String>>) {
    let sols = derived(out, "solution")
        .map(|a| sym(a, "p").unwrap().to_string())
        .collect();
    let mut broken: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for a in derived(out, "law_broken") {
        broken
            .entry(sym(a, "law").unwrap().to_string())
            .or_default()
            .push(format!("{}·{}", sym(a, "a").unwrap(), sym(a, "b").unwrap()));
    }
    (sols, broken)
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect("problem file");
    let seed: u64 = args.next().map(|s| s.parse().expect("seed")).unwrap_or(1);
    let force = args.next().as_deref() == Some("force");
    let src = agl::read_expanded(Path::new(&path)).unwrap();
    let base = agl::parse(&src).unwrap();
    let dom = base
        .facts
        .iter()
        .find(|f| f.atom.rel == "domain")
        .expect("domain(lo, hi)");
    let (lo, hi) = (
        num(&dom.atom, "lo").unwrap() as i64,
        num(&dom.atom, "hi").unwrap() as i64,
    );

    // 1. The old domain and the anomaly.
    let mut text = src.clone();
    for a in lo..=hi {
        text.push_str(&poly("coef", "e", a, 0));
    }
    for k0 in -K..=K {
        for k1 in -K..=K {
            text.push_str(&poly("mult", "u", k0, k1));
        }
    }
    let prog = agl::parse(&text).unwrap();
    let report = agl::run(&prog);
    let failed: Vec<Atom> = report
        .failed_queries()
        .map(|q| q.query.atom.clone())
        .collect();
    println!(
        "old domain {lo}..{hi}; anomaly: {:?}",
        failed.iter().map(|a| a.to_string()).collect::<Vec<_>>()
    );
    let declared = base.facts.iter().find(|f| f.atom.rel == "equation");
    let eq = match failed.iter().find_map(|a| sym(a, "eq")) {
        Some(eq) => eq.to_string(),
        None if force => {
            println!("no anomaly; adjoining anyway (control)");
            sym(&declared.expect("equation").atom, "eq")
                .unwrap()
                .to_string()
        }
        None => {
            println!("no anomaly, nothing to adjoin");
            return;
        }
    };
    let (_, root_broken) = sieve(&evaluate(&prog, &Plane::new()));

    // 2. Adjoin exactly the equation that failed.
    text.push_str(&format!(
        "axis repr\nvalue repr adj\nplane adj = repr:adj\nfact adj: adjoined(eq: {eq}) @ adj\n"
    ));
    let mut elems: Vec<(i64, i64)> = Vec::new();
    for a in lo..=hi {
        for b in lo..=hi {
            elems.push((a, b));
            if b != 0 {
                text.push_str(&poly("coef", "e", a, b));
            }
        }
    }
    let mut rng = Rng::new(seed);
    let mut probes = std::collections::BTreeSet::new();
    for _ in 0..PROBES {
        probes.insert((*rng.pick(&elems), *rng.pick(&elems)));
    }
    for (x, y) in &probes {
        let (l, r) = (name("e", x.0, x.1), name("e", y.0, y.1));
        text.push_str(&format!("fact pr_{l}_{r}: probe(l: {l}, r: {r}) @\n"));
    }
    let prog = agl::parse(&text).unwrap();
    let out = evaluate(&prog, &prog.planes["adj"]);
    let (sols, broken) = sieve(&out);

    println!(
        "plane adj: X with {eq} adjoined; {} elements, {} probes",
        elems.len(),
        probes.len()
    );
    println!(
        "  root, laws broken: {:?}",
        root_broken.keys().collect::<Vec<_>>()
    );
    println!("  (1) solutions: {sols:?}");
    for law in ["conservative", "cancellation"] {
        match broken.get(law) {
            None => println!("  {law}: kept"),
            Some(v) => println!(
                "  {law}: broken {} times, e.g. {:?}",
                v.len(),
                &v[..v.len().min(4)]
            ),
        }
    }
}

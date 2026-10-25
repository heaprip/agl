//! Step 4 of the ladder H57: Hamilton's question. Extend the complex numbers
//! by more imaginary units, keeping the laws; when no table keeps them all,
//! drop a law.
//!
//! The case `cases/discovery/hamilton.agl` knows the bilinear product by a
//! table of units, u0 as the unit and u² = −1 for every imaginary unit, and
//! how to check three laws. The generator walks levels by economy: fewer
//! dropped laws first, then the smaller dimension. At each level it searches
//! in two stages: (A) for every pair of imaginary units, all values of
//! (uₐu_b, u_buₐ) among ±u_k, checked by the kernel inside the pair; (B) the
//! products of surviving pair tables, checked by the kernel in full. It stops
//! at the first level where some table survives.
//!
//!     cargo run --release --example hamilton            # seed 1
//!     cargo run --release --example hamilton -- 7       # another seed
//!     cargo run --release --example hamilton -- 1 free-squares zero
//!
//! The ablation of the givens (H57, after step 4): `free-squares` lets the
//! squares of u2, u3 be −1, 0 or +1 (u1² = −1 stays: that is i); `zero` lets
//! a product of units be zero.
//!
//! Criterion declared before the run: docs/hypotheses.md, H57, step 4.

use std::collections::BTreeSet;

use agl::eval::evaluate;
use agl::model::{Plane, Term};
use agl::sim::Rng;

const CASE: &str = "cases/discovery/hamilton.agl";
const LAWS: [&str; 3] = ["commutative", "associative", "norm"];
const PROBES_A: usize = 100;
const PROBES_B: usize = 150;
/// Tables per kernel run, so that the closure stays under the kernel's atom
/// limit (a truncated run is an error, not an answer).
const CHUNK: usize = 32;

/// A value ±u_k.
type Val = (i64, usize);

fn val(v: Val) -> String {
    match v.0 {
        0 => "0".into(),
        1 => format!("+u{}", v.1),
        _ => format!("-u{}", v.1),
    }
}

fn tag(v: Val) -> String {
    match v.0 {
        0 => "z".into(),
        1 => format!("p{}", v.1),
        _ => format!("m{}", v.1),
    }
}

/// Elements with coefficients in {−1, 0, 1} on the given units, nonzero.
fn elements(n: usize, units: &[usize]) -> Vec<Vec<i64>> {
    let mut out = vec![vec![0; n]];
    for &u in units {
        out = out
            .into_iter()
            .flat_map(|e| {
                [-1, 0, 1].map(|c| {
                    let mut e = e.clone();
                    e[u] = c;
                    e
                })
            })
            .collect();
    }
    out.retain(|e| e.iter().any(|&c| c != 0));
    out
}

fn ename(e: &[i64]) -> String {
    let s: String = e
        .iter()
        .map(|c| match c {
            -1 => 'm',
            0 => 'z',
            _ => 'p',
        })
        .collect();
    format!("x_{s}")
}

fn element(e: &[i64]) -> String {
    let p = ename(e);
    e.iter()
        .enumerate()
        .filter(|(_, c)| **c != 0)
        .map(|(u, c)| format!("fact {p}_{u}: coef(p: {p}, u: u{u}, c: {c}) @\n"))
        .collect()
}

/// A table: entries (a, b, value) beyond the given ones.
type Table = Vec<(usize, usize, Val)>;

/// Runs the kernel on `tables` in one scope; returns the survivors.
#[allow(clippy::too_many_arguments)]
fn check(
    src: &str,
    n: usize,
    fixed: &[usize],
    active: &[&str],
    scope: &str,
    tables: &[(String, Table)],
    probes: &[(Vec<i64>, Vec<i64>)],
) -> Vec<String> {
    let mut text = src.to_string();
    for u in 0..n {
        text.push_str(&format!("fact unit_{u}: unit(u: u{u}) @\n"));
    }
    for u in fixed {
        text.push_str(&format!("fact sq_{u}: fixed_square(u: u{u}) @\n"));
    }
    for l in active {
        text.push_str(&format!("fact active_{l}: active(law: {l}) @\n"));
    }
    for (t, entries) in tables {
        text.push_str(&format!("fact {t}: table(t: {t}, scope: {scope}) @\n"));
        for (a, b, v) in entries {
            text.push_str(&format!(
                "fact {t}_{a}_{b}: entry(t: {t}, a: u{a}, b: u{b}, s: {}, c: u{}) @\n",
                v.0, v.1
            ));
        }
    }
    if active.contains(&"norm") {
        let mut named = BTreeSet::new();
        for (x, y) in probes {
            for e in [x, y] {
                if named.insert(e.clone()) {
                    text.push_str(&element(e));
                }
            }
            let (px, py) = (ename(x), ename(y));
            text.push_str(&format!(
                "fact pr_{scope}_{px}_{py}: probe(scope: {scope}, x: {px}, y: {py}) @\n"
            ));
        }
    }
    let prog = agl::parse(&text).unwrap();
    let out = evaluate(&prog, &Plane::new());
    assert!(!out.truncated, "closure truncated: raise the batch split");
    out.db
        .values()
        .filter(|(a, _)| a.rel == "survives" && !a.neg)
        .filter_map(|(a, _)| match &a.args[0].1 {
            Term::Sym(t) => Some(t.to_string()),
            _ => None,
        })
        .collect()
}

fn sample(rng: &mut Rng, elems: &[Vec<i64>], k: usize) -> Vec<(Vec<i64>, Vec<i64>)> {
    let mut set = BTreeSet::new();
    for _ in 0..k {
        set.insert((rng.pick(elems).clone(), rng.pick(elems).clone()));
    }
    set.into_iter().collect()
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let seed: u64 = args.first().map(|s| s.parse().expect("seed")).unwrap_or(1);
    let free_squares = args.iter().any(|a| a == "free-squares");
    let zero = args.iter().any(|a| a == "zero");
    let src = std::fs::read_to_string(CASE).unwrap();
    let mut rng = Rng::new(seed);

    for dropped in 0..LAWS.len() {
        let mut found = false;
        for n in [3, 4] {
            let mut values: Vec<Val> = (0..n).flat_map(|k| [(1, k), (-1, k)]).collect();
            if zero {
                values.push((0, 0));
            }
            let squares: Vec<Val> = if free_squares {
                vec![(-1, 0), (0, 0), (1, 0)]
            } else {
                vec![(-1, 0)]
            };
            let fixed: Vec<usize> = if free_squares {
                vec![1]
            } else {
                (1..n).collect()
            };
            let free = |u: usize| free_squares && u >= 2;
            let drops: Vec<Vec<&str>> = (0..1u32 << LAWS.len())
                .filter(|m| m.count_ones() as usize == dropped)
                .map(|m| {
                    (0..LAWS.len())
                        .filter(|i| m >> i & 1 == 1)
                        .map(|i| LAWS[i])
                        .collect()
                })
                .collect();
            for drop in drops {
                let active: Vec<&str> =
                    LAWS.iter().copied().filter(|l| !drop.contains(l)).collect();
                // Stage A: pairs of imaginary units.
                let mut per_pair: Vec<Vec<Table>> = Vec::new();
                for a in 1..n {
                    for b in a + 1..n {
                        let scope = format!("s{a}{b}");
                        let sq = |u: usize| -> Vec<Option<Val>> {
                            if free(u) {
                                squares.iter().map(|&q| Some(q)).collect()
                            } else {
                                vec![None]
                            }
                        };
                        let mut tables: Vec<(String, Table)> = Vec::new();
                        for &v in &values {
                            for &w in &values {
                                for qa in sq(a) {
                                    for qb in sq(b) {
                                        let mut t = vec![(a, b, v), (b, a, w)];
                                        let mut name = format!("{scope}_{}_{}", tag(v), tag(w));
                                        for (u, q) in [(a, qa), (b, qb)] {
                                            if let Some(q) = q {
                                                t.push((u, u, q));
                                                name.push_str(&format!("_q{u}{}", tag(q)));
                                            }
                                        }
                                        tables.push((name, t));
                                    }
                                }
                            }
                        }
                        let probes = sample(&mut rng, &elements(n, &[0, a, b]), PROBES_A);
                        let mut alive = Vec::new();
                        for chunk in tables.chunks(CHUNK) {
                            alive.extend(check(&src, n, &fixed, &active, &scope, chunk, &probes));
                        }
                        per_pair.push(
                            tables
                                .into_iter()
                                .filter(|(t, _)| alive.contains(t))
                                .map(|(_, e)| e)
                                .collect(),
                        );
                    }
                }
                // Stage B: full tables from the surviving pairs.
                let mut full: Vec<Table> = vec![vec![]];
                for pair in &per_pair {
                    full = full
                        .iter()
                        .flat_map(|t| {
                            pair.iter().filter_map(move |p| {
                                let mut t = t.clone();
                                for &(a, b, v) in p {
                                    match t.iter().find(|e| e.0 == a && e.1 == b) {
                                        Some(e) if e.2 != v => return None,
                                        Some(_) => {}
                                        None => t.push((a, b, v)),
                                    }
                                }
                                Some(t)
                            })
                        })
                        .collect();
                }
                let tables: Vec<(String, Table)> = full
                    .into_iter()
                    .enumerate()
                    .map(|(i, t)| (format!("f{i}"), t))
                    .collect();
                let all: Vec<usize> = (0..n).collect();
                let probes = sample(&mut rng, &elements(n, &all), PROBES_B);
                let mut alive = Vec::new();
                for chunk in tables.chunks(CHUNK) {
                    alive.extend(check(&src, n, &fixed, &active, "all", chunk, &probes));
                }
                println!(
                    "n = {n}, dropped {drop:?}: pair stage {:?}, full tables {}, survive {}",
                    per_pair.iter().map(Vec::len).collect::<Vec<_>>(),
                    tables.len(),
                    alive.len()
                );
                for (t, entries) in tables.iter().filter(|(t, _)| alive.contains(t)) {
                    let text: Vec<String> = entries
                        .iter()
                        .map(|(a, b, v)| format!("u{a}u{b} = {}", val(*v)))
                        .collect();
                    println!("  {t}: {}", text.join(", "));
                    found = true;
                }
            }
            if found {
                println!(
                    "stopped: first level with survivors is n = {n}, {dropped} law(s) dropped"
                );
                return;
            }
        }
    }
    println!("no table survives at any level");
}

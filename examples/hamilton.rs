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

/// A value ±u_k.
type Val = (i64, usize);

fn val(v: Val) -> String {
    format!("{}u{}", if v.0 > 0 { "+" } else { "-" }, v.1)
}

fn tag(v: Val) -> String {
    format!("{}{}", if v.0 > 0 { "p" } else { "m" }, v.1)
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
fn check(
    src: &str,
    n: usize,
    active: &[&str],
    scope: &str,
    tables: &[(String, Table)],
    probes: &[(Vec<i64>, Vec<i64>)],
) -> Vec<String> {
    let mut text = src.to_string();
    for u in 0..n {
        text.push_str(&format!("fact unit_{u}: unit(u: u{u}) @\n"));
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
    out.db
        .values()
        .filter(|(a, _)| a.rel == "survives" && !a.neg)
        .filter_map(|(a, _)| match &a.args[0].1 {
            Term::Sym(t) => Some(t.clone()),
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
    let seed: u64 = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("seed"))
        .unwrap_or(1);
    let src = std::fs::read_to_string(CASE).unwrap();
    let mut rng = Rng::new(seed);

    for dropped in 0..LAWS.len() {
        let mut found = false;
        for n in [3, 4] {
            let values: Vec<Val> = (0..n).flat_map(|k| [(1, k), (-1, k)]).collect();
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
                        let tables: Vec<(String, Table)> = values
                            .iter()
                            .flat_map(|&v| values.iter().map(move |&w| (v, w)))
                            .map(|(v, w)| {
                                (
                                    format!("{scope}_{}_{}", tag(v), tag(w)),
                                    vec![(a, b, v), (b, a, w)],
                                )
                            })
                            .collect();
                        let probes = sample(&mut rng, &elements(n, &[0, a, b]), PROBES_A);
                        let alive = check(&src, n, &active, &scope, &tables, &probes);
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
                            pair.iter().map(move |p| {
                                let mut t = t.clone();
                                t.extend(p.iter().copied());
                                t
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
                let alive = if tables.is_empty() {
                    vec![]
                } else {
                    check(&src, n, &active, "all", &tables, &probes)
                };
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

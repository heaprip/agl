//! The Bombelli step (H53): an anomaly, a change of plane, a search checked
//! by the kernel, and the way back to ordinary numbers.
//!
//! The kernel runs `cases/discovery/bombelli.agl`. An expectation that fails
//! is an anomaly; the planes whose rules use a relation the failed rule
//! depends on are mobilized. Here that is the plane of pairs, where a square
//! root of a negative radicand is a pair. The generator adds integer pairs
//! |a|, |b| <= BOUND in an order drawn from the seed, a batch at a time,
//! until the kernel answers the failed question in the mobilized plane.
//!
//!     cargo run --release --example bombelli            # seed 1
//!     cargo run --release --example bombelli -- 7       # another seed
//!     AGL_TRACE=1 cargo run --release --example bombelli  # every batch
//!
//! Criterion declared before the run: docs/hypotheses.md, H53, the Bombelli
//! step. Nothing is written to disk: the trace is recomputed from the seed.

use std::collections::BTreeSet;

use agl::eval::evaluate;
use agl::model::{Lit, Program, Verdict};
use agl::sim::Rng;

const CASE: &str = "cases/discovery/bombelli.agl";
const BOUND: i64 = 10;
const BATCH: usize = 50;

/// Relations a rule for `rel` uses in its body, in any plane.
fn premises(prog: &Program, rel: &str) -> BTreeSet<String> {
    prog.rules
        .iter()
        .filter(|r| r.head.rel == rel)
        .flat_map(|r| &r.body)
        .filter_map(|l| match l {
            Lit::Atom(a) => Some(a.rel.clone()),
            _ => None,
        })
        .collect()
}

fn main() {
    let seed: u64 = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("seed"))
        .unwrap_or(1);
    let trace = std::env::var("AGL_TRACE").is_ok();
    let src = std::fs::read_to_string(CASE).unwrap();
    let base = agl::parse(&src).unwrap();

    // 1. Anomalies: expectations the kernel does not meet without pairs.
    let report = agl::run(&base);
    let failed: Vec<_> = report
        .failed_queries()
        .filter(|q| q.plane.is_empty())
        .map(|q| q.query.atom.rel.clone())
        .collect();
    println!("anomalies at the root: {failed:?}");

    // 2. Mobilization: planes with rules over what the failed rules use.
    let used: BTreeSet<String> = failed.iter().flat_map(|r| premises(&base, r)).collect();
    let mobilized: BTreeSet<&String> = base
        .planes
        .iter()
        .filter(|(_, plane)| {
            base.rules.iter().any(|r| {
                r.plane == **plane
                    && r.body
                        .iter()
                        .any(|l| matches!(l, Lit::Atom(a) if used.contains(&a.rel)))
            })
        })
        .map(|(name, _)| name)
        .collect();
    println!("used by the failed rules: {used:?}; mobilized planes: {mobilized:?}");

    // 3. Search in the mobilized plane: pairs in an order from the seed.
    let mut pairs: Vec<(i64, i64)> = (-BOUND..=BOUND)
        .flat_map(|a| (-BOUND..=BOUND).map(move |b| (a, b)))
        .collect();
    Rng::new(seed).shuffle(&mut pairs);
    for name in mobilized {
        let plane = &base.planes[name];
        let mut text = src.clone();
        for (k, batch) in pairs.chunks(BATCH).enumerate() {
            for (a, b) in batch {
                text.push_str(&format!(
                    "fact p_{}: pair(re: {a}, im: {b}) @ {name}\n",
                    text.len()
                ));
            }
            let prog = agl::parse(&text).unwrap();
            let out = evaluate(&prog, plane);
            assert!(!out.truncated, "closure truncated: raise the batch split");
            let roots: Vec<String> = out
                .db
                .values()
                .filter(|(a, _)| a.rel == "cube_root" && !a.neg)
                .map(|(a, _)| a.to_string())
                .collect();
            let report = agl::run(&prog);
            let answered = report
                .queries
                .iter()
                .filter(|q| q.plane == *plane)
                .all(|q| q.query.expect == Some(q.verdict));
            if trace {
                println!(
                    "  batch {}: {} pairs tried, cube roots found: {roots:?}",
                    k + 1,
                    ((k + 1) * BATCH).min(pairs.len())
                );
            }
            if answered {
                println!(
                    "plane {name}: answered after {} of {} pairs; cube roots: {roots:?}",
                    ((k + 1) * BATCH).min(pairs.len()),
                    pairs.len()
                );
                for q in report.queries.iter().filter(|q| q.plane == *plane) {
                    let ok = q.verdict == Verdict::Yes;
                    println!(
                        "  {} @ {name} → {:?}{}",
                        q.query.atom,
                        q.verdict,
                        if ok { "" } else { " (!)" }
                    );
                }
                break;
            }
        }
    }
}

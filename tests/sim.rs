//! Deterministic simulation tests. Each run is fully determined by its seed;
//! a failure prints the seed, and `AGL_SEED=<n> cargo test --test sim` replays it.
//! `AGL_SIM_SEEDS=<n>` widens the sweep.

use agl::model::*;
use agl::sim::{Rng, gen_program, permute};

fn seeds() -> Vec<u64> {
    if let Ok(s) = std::env::var("AGL_SEED") {
        return vec![s.parse().expect("AGL_SEED must be a number")];
    }
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500);
    (0..n).collect()
}

#[test]
fn same_seed_same_report() {
    for seed in seeds() {
        let a = agl::render(&agl::run(&gen_program(seed)));
        let b = agl::render(&agl::run(&gen_program(seed)));
        assert_eq!(a, b, "seed {seed}: two runs differ");
    }
}

#[test]
fn statement_order_does_not_matter() {
    for seed in seeds() {
        let prog = gen_program(seed);
        let base = agl::render(&agl::run(&prog));
        for k in 0..3 {
            let shuffled = permute(&prog, seed.wrapping_mul(31).wrapping_add(k));
            let other = agl::render(&agl::run(&shuffled));
            assert_eq!(
                base, other,
                "seed {seed}, permutation {k}: report depends on statement order"
            );
        }
    }
}

#[test]
fn a_visible_fact_is_never_overturned_by_a_defeasible_rule() {
    for seed in seeds() {
        let prog = gen_program(seed);
        for f in &prog.facts {
            let q = Query {
                atom: f.atom.clone(),
                plane: f.plane.clone(),
                expect: None,
                line: 0,
            };
            let mut p = permute(&prog, seed);
            p.queries = vec![q];
            let r = agl::run(&p);
            let v = r.queries[0].verdict;
            assert!(
                v == Verdict::Yes || v == Verdict::Conflict,
                "seed {seed}: fact {} @ {} answered {v}",
                f.id,
                plane_to_string(&f.plane)
            );
        }
    }
}

#[test]
fn adding_a_fact_in_a_disjoint_plane_changes_nothing() {
    for seed in seeds() {
        let prog = gen_program(seed);
        let mut rng = Rng::new(seed ^ 0xA5A5);
        // x1 and y are disjoint on axis w: a fact in y is invisible from x1.
        let mut p = prog;
        p.queries
            .iter_mut()
            .for_each(|q| q.plane = Plane::from([("w".into(), "x1".into())]));
        let before: Vec<Verdict> = agl::run(&p).queries.iter().map(|q| q.verdict).collect();
        let atom = p.queries[rng.below(p.queries.len())].atom.clone();
        p.facts.push(Fact {
            id: "intruder".into(),
            atom: atom.complement(),
            plane: Plane::from([("w".into(), "y".into())]),
            status: "given".into(),
            line: 0,
        });
        let after: Vec<Verdict> = agl::run(&p).queries.iter().map(|q| q.verdict).collect();
        assert_eq!(
            before, after,
            "seed {seed}: a fact in a disjoint plane changed verdicts"
        );
    }
}

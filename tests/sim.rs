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
fn a_visible_fact_is_overturned_only_by_a_more_trusted_strict_derivation() {
    for seed in seeds() {
        let prog = gen_program(seed);
        for f in &prog.facts {
            let p = permute(&prog, seed);
            let out = agl::eval::evaluate(&p, &f.plane);
            if out.db.contains_key(&f.atom.key()) {
                continue;
            }
            let rank = |status: &str| p.status_rank.get(status).copied().unwrap_or(0);
            if out.conflicts.contains_key(&if f.atom.neg {
                f.atom.complement().key()
            } else {
                f.atom.key()
            }) {
                continue;
            }
            let Some((_, derivs)) = out.db.get(&f.atom.complement().key()) else {
                panic!(
                    "seed {seed}: fact {} vanished without being contradicted",
                    f.id
                );
            };
            assert!(
                derivs.iter().any(|d| d.strict && d.rank > rank(&f.status)),
                "seed {seed}: fact {} @ {} overturned by {:?}",
                f.id,
                plane_to_string(&f.plane),
                derivs
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

#[test]
fn real_cases_do_not_depend_on_statement_order() {
    let mut paths: Vec<_> = ["cases", "cases/reflection"]
        .iter()
        .flat_map(|d| std::fs::read_dir(d).unwrap().map(|e| e.unwrap().path()))
        .filter(|p| p.extension().is_some_and(|e| e == "agl"))
        .collect();
    paths.sort();
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500)
        .min(50);
    for path in paths {
        let prog = agl::parse(&std::fs::read_to_string(&path).unwrap()).unwrap();
        let base = agl::render(&agl::run(&prog));
        for seed in 0..n {
            let other = agl::render(&agl::run(&permute(&prog, seed)));
            assert_eq!(
                base,
                other,
                "{} seed {seed}: report depends on statement order",
                path.display()
            );
        }
    }
}

#[test]
fn diagnosis_is_deterministic_and_order_independent() {
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500)
        .min(300);
    let seeds: Vec<u64> = match std::env::var("AGL_SEED") {
        Ok(s) => vec![s.parse().unwrap()],
        Err(_) => (0..n).collect(),
    };
    for seed in seeds {
        let prog = gen_program(seed);
        let base = agl::reflect::render(&agl::reflect::diagnose(&prog));
        assert_eq!(
            base,
            agl::reflect::render(&agl::reflect::diagnose(&prog)),
            "seed {seed}: two runs differ"
        );
        let other = agl::reflect::render(&agl::reflect::diagnose(&permute(&prog, seed + 7)));
        assert_eq!(
            base, other,
            "seed {seed}: diagnosis depends on statement order"
        );
    }
}

#[test]
fn proposals_never_make_expectations_worse_and_do_not_depend_on_order() {
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(500)
        .min(150);
    let seeds: Vec<u64> = match std::env::var("AGL_SEED") {
        Ok(s) => vec![s.parse().unwrap()],
        Err(_) => (0..n).collect(),
    };
    for seed in seeds {
        // Expectations: the current answer, flipped for some queries, so that
        // there is something to repair.
        let mut prog = gen_program(seed);
        let mut rng = Rng::new(seed ^ 0x5EED);
        let answers: Vec<Verdict> = agl::run(&prog).queries.iter().map(|q| q.verdict).collect();
        for (q, v) in prog.queries.iter_mut().zip(answers) {
            q.expect = Some(if rng.chance(1, 3) {
                match v {
                    Verdict::Yes => Verdict::No,
                    Verdict::No | Verdict::Unknown | Verdict::Conflict => Verdict::Yes,
                    Verdict::Gap => Verdict::Gap,
                }
            } else {
                v
            });
        }
        let (ps, notes) = agl::propose::propose(&prog);
        let base = agl::propose::render(&ps, &notes);
        let (ps2, notes2) = agl::propose::propose(&permute(&prog, seed + 3));
        assert_eq!(
            base,
            agl::propose::render(&ps2, &notes2),
            "seed {seed}: proposals depend on statement order"
        );
        let before = agl::run(&prog);
        for p in &ps {
            let after = agl::run(&agl::propose::apply(&prog, &p.op).unwrap());
            for (b, a) in before.queries.iter().zip(&after.queries) {
                if b.query.expect == Some(b.verdict) {
                    assert_eq!(
                        a.query.expect,
                        Some(a.verdict),
                        "seed {seed}: {:?} broke a met expectation",
                        p.op
                    );
                }
            }
            assert!(p.after >= p.before, "seed {seed}: {:?}", p.op);
        }
    }
}

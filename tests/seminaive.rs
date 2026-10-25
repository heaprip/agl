//! Semi-naive evaluation against the naive reference (H65): every closure
//! must hold the same atoms with the same derivations, conflicts and errors.
//! `AGL_SIM_SEEDS=<n>` widens the sweep, `AGL_SEED=<n>` replays one seed.

use std::collections::BTreeSet;

use agl::eval::{Outcome, evaluate, evaluate_reference};
use agl::model::{Plane, Program};
use agl::sim::gen_program;

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

fn text(out: &Outcome) -> String {
    let mut s = String::new();
    for (k, (_, ds)) in &out.db {
        let mut ds: Vec<String> = ds
            .iter()
            .map(|d| {
                format!(
                    "{} {} {} {:?} {:?}",
                    d.source,
                    d.strict,
                    d.rank,
                    d.plane,
                    out.db.premise_keys(d).collect::<Vec<_>>()
                )
            })
            .collect();
        ds.sort();
        s += &format!("{k}: {ds:?}\n");
    }
    s + &format!(
        "{:?}\n{:?}\n{:?}\n{}\n",
        out.conflicts, out.defeated, out.errors, out.truncated
    )
}

/// The empty plane and every plane a statement or a named plane uses.
fn planes(prog: &Program) -> BTreeSet<Plane> {
    let mut ps: BTreeSet<Plane> = BTreeSet::from([Plane::new()]);
    ps.extend(prog.facts.iter().map(|f| f.plane.clone()));
    ps.extend(prog.rules.iter().map(|r| r.plane.clone()));
    ps.extend(prog.planes.values().cloned());
    ps
}

fn same(prog: &Program, what: &str) -> usize {
    let mut n = 0;
    for p in planes(prog) {
        let fast = evaluate(prog, &p);
        let slow = evaluate_reference(prog, &p);
        assert_eq!(text(&fast), text(&slow), "{what}, plane {p:?}");
        n += 1;
    }
    n
}

#[test]
fn semi_naive_equals_naive_on_random_programs() {
    for seed in seeds() {
        same(&gen_program(seed), &format!("seed {seed}"));
    }
}

fn agl_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            agl_files(&p, out);
        } else if p.extension().is_some_and(|e| e == "agl") {
            out.push(p);
        }
    }
}

#[test]
fn semi_naive_equals_naive_on_cases() {
    let mut files = Vec::new();
    agl_files(std::path::Path::new("cases"), &mut files);
    let mut checked = 0;
    for f in &files {
        // Library files are included by cases, not run alone.
        let Ok(prog) = agl::parse_file(f) else {
            continue;
        };
        checked += same(&prog, &f.display().to_string());
    }
    assert!(checked > 50, "only {checked} closures checked");
}

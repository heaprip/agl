//! Reference semantics: a slow, literal defeasible logic evaluator, checked
//! against the kernel on generated programs without planes and aggregates.
//!
//! The evaluator follows the proof conditions +Δ/−Δ/+∂/−∂ of Antoniou,
//! Billington, Governatori and Maher, "Representation results for defeasible
//! logic" (ACM TOCL 2001): ambiguity blocking, team defeat, `defeats` as the
//! superiority relation. Two departures, both stated in poc:
//!
//! - failure is well-founded: a literal whose every rule rests on an
//!   unfounded loop is refuted, as the kernel's least fixpoint does;
//! - trust: when `p` and `¬p` are both strictly derivable, the side with the
//!   more trusted strict proof wins (the rank of a proof is its least trusted
//!   fact, the rank of a literal its best proof); equal ranks block both.
//!
//! Programs where the kernel's documented semantics goes beyond these
//! definitions are skipped and counted, not compared: a strict contradiction
//! with consequences (the kernel blocks the consequences, DL keeps them), a
//! defeasible conflict under statuses (the kernel ranks before `defeats`, an
//! open question of the author), and literals the definitions leave undecided.

use std::collections::{BTreeMap, BTreeSet};

use agl::eval::subst;
use agl::model::*;
use agl::sim::gen_flat_program;

struct GRule {
    id: String,
    strict: bool,
    head: String,
    body: Vec<String>,
}

struct Theory {
    /// Every literal in play and its complement.
    comp: BTreeMap<String, String>,
    /// Fact literal -> its best status rank.
    facts: BTreeMap<String, usize>,
    rules: Vec<GRule>,
    sup: BTreeSet<(String, String)>,
}

fn ground(prog: &Program) -> Theory {
    let mut consts = BTreeSet::new();
    let mut atoms: Vec<&Atom> = prog.facts.iter().map(|f| &f.atom).collect();
    for r in &prog.rules {
        atoms.push(&r.head);
        for l in &r.body {
            if let Lit::Atom(a) = l {
                atoms.push(a);
            }
        }
    }
    for a in &atoms {
        for (_, t) in &a.args {
            if let Term::Sym(s) = t {
                consts.insert(s.clone());
            }
        }
    }
    let consts: Vec<String> = consts.into_iter().collect();
    let mut comp = BTreeMap::new();
    let mut note = |a: &Atom| {
        comp.insert(a.key(), a.complement().key());
        comp.insert(a.complement().key(), a.key());
    };
    let mut facts = BTreeMap::new();
    for f in &prog.facts {
        note(&f.atom);
        let rank = prog.status_rank.get(&f.status).copied().unwrap_or(0);
        let best = facts.entry(f.atom.key()).or_insert(rank);
        *best = (*best).max(rank);
    }
    let mut rules = Vec::new();
    for r in &prog.rules {
        let body: Vec<&Atom> = r
            .body
            .iter()
            .map(|l| match l {
                Lit::Atom(a) => a,
                _ => panic!("the reference covers atoms only"),
            })
            .collect();
        let vars: BTreeSet<String> = body
            .iter()
            .flat_map(|a| a.vars())
            .chain(r.head.vars())
            .map(str::to_string)
            .collect();
        let vars: Vec<String> = vars.into_iter().collect();
        let mut idx = vec![0; vars.len()];
        loop {
            let b: BTreeMap<String, Term> = vars
                .iter()
                .zip(&idx)
                .map(|(v, &i)| (v.clone(), Term::Sym(consts[i].clone())))
                .collect();
            let head = subst(&r.head, &b);
            let gbody: Vec<Atom> = body.iter().map(|a| subst(a, &b)).collect();
            note(&head);
            gbody.iter().for_each(&mut note);
            let mut keys: Vec<String> = gbody.iter().map(Atom::key).collect();
            keys.sort();
            keys.dedup();
            rules.push(GRule {
                id: r.id.clone(),
                strict: r.strength == Strength::Strict,
                head: head.key(),
                body: keys,
            });
            // Next assignment, odometer style.
            let mut k = 0;
            while k < idx.len() {
                idx[k] += 1;
                if idx[k] < consts.len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
            if k == idx.len() {
                break;
            }
        }
    }
    Theory {
        comp,
        facts,
        rules,
        sup: prog.defeats.clone(),
    }
}

/// What the reference concludes, or why it declines to.
enum Answer {
    /// +∂, and +Δ.
    Proved(BTreeSet<String>, BTreeSet<String>),
    Skip(&'static str),
}

fn reference(th: &Theory) -> Answer {
    // +Δ: facts closed under strict rules; rank: the best strict proof.
    let mut delta: BTreeMap<String, usize> = th.facts.clone();
    loop {
        let mut changed = false;
        for r in th.rules.iter().filter(|r| r.strict) {
            let Some(rank) = r
                .body
                .iter()
                .map(|b| delta.get(b).copied())
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let rank = rank.into_iter().min().unwrap_or(usize::MAX);
            let cur = delta.get(&r.head).copied();
            if cur.is_none_or(|c| rank > c) {
                delta.insert(r.head.clone(), rank);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let in_delta = |q: &str| delta.contains_key(q);
    // A strict contradiction with consequences: outside the compared fragment.
    let used: BTreeSet<&String> = th.rules.iter().flat_map(|r| &r.body).collect();
    for q in delta.keys() {
        if in_delta(&th.comp[q]) && (used.contains(q) || used.contains(&th.comp[q])) {
            return Answer::Skip("strict contradiction with consequences");
        }
    }
    let strictly_wins = |q: &str| {
        let Some(&r) = delta.get(q) else {
            return false;
        };
        delta.get(&th.comp[q]).is_none_or(|&c| r > c)
    };
    let mut by_head: BTreeMap<&str, Vec<&GRule>> = BTreeMap::new();
    for r in &th.rules {
        by_head.entry(&r.head).or_default().push(r);
    }
    let none = Vec::new();
    let rules_for = |q: &str| by_head.get(q).unwrap_or(&none).iter().copied();
    let sup = |t: &GRule, s: &GRule| th.sup.contains(&(t.id.clone(), s.id.clone()));

    let mut plus: BTreeSet<String> = BTreeSet::new();
    let mut minus: BTreeSet<String> = BTreeSet::new();
    let lits: Vec<&String> = th.comp.keys().collect();
    loop {
        let mut changed = false;
        for &q in &lits {
            let nq = &th.comp[q];
            let applicable =
                |r: &GRule, plus: &BTreeSet<String>| r.body.iter().all(|b| plus.contains(b));
            let discarded =
                |r: &GRule, minus: &BTreeSet<String>| r.body.iter().any(|b| minus.contains(b));
            if !plus.contains(q) {
                let defeasibly = !in_delta(nq)
                    && rules_for(q).any(|r| applicable(r, &plus))
                    && rules_for(nq).all(|s| {
                        discarded(s, &minus)
                            || rules_for(q).any(|t| applicable(t, &plus) && sup(t, s))
                    });
                if strictly_wins(q) || defeasibly {
                    plus.insert(q.clone());
                    changed = true;
                }
            }
            if !minus.contains(q) && !strictly_wins(q) {
                let refuted = in_delta(nq)
                    || rules_for(q).all(|r| discarded(r, &minus))
                    || rules_for(nq).any(|s| {
                        applicable(s, &plus)
                            && rules_for(q).all(|t| discarded(t, &minus) || !sup(t, s))
                    });
                if refuted {
                    minus.insert(q.clone());
                    changed = true;
                }
            }
        }
        // Well-founded failure: what cannot be supported without a loop.
        let mut possible: BTreeSet<&String> = BTreeSet::new();
        loop {
            let before = possible.len();
            for &q in &lits {
                if !minus.contains(q)
                    && (in_delta(q)
                        || rules_for(q).any(|r| r.body.iter().all(|b| possible.contains(b))))
                {
                    possible.insert(q);
                }
            }
            if possible.len() == before {
                break;
            }
        }
        for &q in &lits {
            if !possible.contains(q) && minus.insert(q.clone()) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if lits
        .iter()
        .any(|q| !plus.contains(*q) && !minus.contains(*q))
    {
        return Answer::Skip("undecided literal");
    }
    Answer::Proved(plus, delta.into_keys().collect())
}

/// Defeasible conflicts the kernel settles by trust before `defeats`.
fn ranked_defeasible_conflict(
    th: &Theory,
    plus: &BTreeSet<String>,
    delta: &BTreeSet<String>,
) -> bool {
    let applicable = |q: &str| {
        th.rules
            .iter()
            .any(|r| r.head == q && r.body.iter().all(|b| plus.contains(b)))
    };
    th.comp
        .iter()
        .any(|(q, nq)| !delta.contains(q) && !delta.contains(nq) && applicable(q) && applicable(nq))
}

fn source(prog: &Program) -> String {
    let mut s = String::new();
    if !prog.status_rank.is_empty() {
        s.push_str("status hi > mid > lo\n");
    }
    for f in &prog.facts {
        s.push_str(&format!("fact {}: {} @ [{}]\n", f.id, f.atom, f.status));
    }
    for r in &prog.rules {
        s.push_str(&r.to_source());
        s.push('\n');
    }
    for (w, l) in &prog.defeats {
        s.push_str(&format!("defeats {w} {l}\n"));
    }
    s
}

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

fn compare(ranked: bool) {
    let mut skipped: BTreeMap<&str, usize> = BTreeMap::new();
    let mut compared = 0;
    let mut failures = Vec::new();
    for seed in seeds() {
        let prog = gen_flat_program(seed, ranked);
        let th = ground(&prog);
        let (plus, delta) = match reference(&th) {
            Answer::Proved(p, d) => (p, d),
            Answer::Skip(why) => {
                *skipped.entry(why).or_default() += 1;
                continue;
            }
        };
        if ranked && ranked_defeasible_conflict(&th, &plus, &delta) {
            *skipped
                .entry("defeasible conflict under statuses")
                .or_default() += 1;
            continue;
        }
        compared += 1;
        let out = agl::eval::evaluate(&prog, &Plane::new());
        let kernel: BTreeSet<String> = out.db.keys().cloned().collect();
        if kernel != plus {
            let only_k: Vec<&String> = kernel.difference(&plus).collect();
            let only_r: Vec<&String> = plus.difference(&kernel).collect();
            failures.push(format!(
                "seed {seed}: kernel only {only_k:?}, reference only {only_r:?}\n{}",
                source(&prog)
            ));
        }
    }
    eprintln!(
        "ranked={ranked}: compared {compared}, skipped {skipped:?}, differ {}",
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} of {compared} programs differ from the reference; first:\n{}",
        failures.len(),
        failures[..failures.len().min(
            std::env::var("AGL_SHOW")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(3)
        )]
            .join("\n")
    );
}

#[test]
fn kernel_agrees_with_reference_defeasible_logic() {
    compare(false);
}

#[test]
fn kernel_agrees_with_reference_under_statuses() {
    compare(true);
}

/// The reference itself on the review's reproductions: it must see the defects.
#[test]
fn reference_sees_the_reviewed_defects() {
    let dir = "docs/review/2026-10-24-repro";
    for (name, want) in [
        ("b1_stale_strict", "q(x: k)"),
        ("b1_control", "q(x: k)"),
        ("b2_lost_opponent", "¬q(x: k)"),
        ("b5_stale_conflict", "¬q(x: k)"),
        ("b4_rank_borrow", "¬q(x: k)"),
        ("b4_control", "¬q(x: k)"),
    ] {
        let prog = agl::parse_file(std::path::Path::new(&format!("{dir}/{name}.agl"))).unwrap();
        let Answer::Proved(plus, _) = reference(&ground(&prog)) else {
            panic!("{name}: the reference declined");
        };
        assert!(
            plus.contains(want),
            "{name}: reference misses {want}: {plus:?}"
        );
    }
}

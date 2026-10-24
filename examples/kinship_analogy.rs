//! Prototype outside the kernel (H51), second test: analogy over relations.
//!
//! Each leaf concept of `cases/kinship.agl` (one definition, no plane, used
//! by no other concept) is removed in turn. The remaining concepts with one
//! sense are taken in normal form, down to primitives. An edit replaces one
//! atom of a normal form by an atom of a primitive relation over the same
//! variables: `female(?x)` → `male(?x)`, `parenthood` turned around. An edit
//! that takes an existing concept A to an existing concept C is a pair A : C.
//! The same edit applied to a concept B gives a candidate D, A : C :: B : D.
//! Candidates equal to no existing concept are ranked by support: for every
//! way (B, edit) to reach D, the number of pairs A : C with that edit
//! (systematicity, Gentner 1983).
//!
//!     cargo run --release --example kinship_analogy
//!
//! Criterion declared before the run (docs/hypotheses.md, H51): the removed
//! concept is among the top 3 candidates for at least two thirds of the
//! removed concepts. Result: 9 of 19, see docs/review/2026-10-24-kinship-analogy.md.
//! `AGL_SHOW=1` prints the top candidates of every run.

use std::collections::{BTreeMap, BTreeSet};

use agl::concept::{CAtom, Cq, T, minimize, normal_form};
use agl::model::{Lit, Plane, Program};

const TOP: usize = 3;
const SHOWN: usize = 8;

/// An edit up to the names of variables: the replaced atom and the new one,
/// variables numbered by first appearance in the replaced atom.
type Edit = (String, String);

/// A concept by its meaning: the sorted texts of its minimized senses.
type Meaning = Vec<String>;

/// An edit, the meaning it gives and the edited query.
type Edited = (Edit, Meaning, Cq);

fn meaning(senses: &[Cq]) -> Meaning {
    let mut m: Meaning = senses.iter().map(|q| q.to_string()).collect();
    m.sort();
    m
}

fn var_order(a: &CAtom) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for (_, t) in &a.args {
        if let T::V(v) = t
            && !out.contains(v)
        {
            out.push(v.clone());
        }
    }
    out
}

fn pattern(a: &CAtom, vars: &[String]) -> String {
    let args: Vec<String> = a
        .args
        .iter()
        .map(|(r, t)| match t {
            T::V(v) => format!("{r}: #{}", vars.iter().position(|x| x == v).unwrap()),
            T::C(c) => format!("{r}: {c}"),
        })
        .collect();
    format!("{}({})", a.rel, args.join(", "))
}

/// Every atom of a primitive relation over exactly the variables of `a`.
fn replacements(prog: &Program, a: &CAtom) -> Vec<CAtom> {
    let vars = var_order(a);
    if vars.len() != a.args.len() {
        return vec![];
    }
    let mut out = Vec::new();
    for (rel, roles) in &prog.relations {
        if roles.len() != vars.len() {
            continue;
        }
        let mut order: Vec<usize> = (0..vars.len()).collect();
        loop {
            let b = CAtom {
                rel: rel.clone(),
                args: roles
                    .iter()
                    .zip(&order)
                    .map(|(r, &i)| (r.clone(), T::V(vars[i].clone())))
                    .collect(),
            };
            if b != *a {
                out.push(b);
            }
            if !next_permutation(&mut order) {
                break;
            }
        }
    }
    out
}

fn next_permutation(v: &mut [usize]) -> bool {
    let Some(i) = (1..v.len()).rev().find(|&i| v[i - 1] < v[i]) else {
        return false;
    };
    let j = (i..v.len()).rev().find(|&j| v[j] > v[i - 1]).unwrap();
    v.swap(i - 1, j);
    v[i..].reverse();
    true
}

/// Every single-atom edit of a sense, with the edited query minimized.
fn edits(prog: &Program, q: &Cq) -> Vec<Edited> {
    let root = Plane::new();
    let mut out = Vec::new();
    for (i, a) in q.atoms.iter().enumerate() {
        let vars = var_order(a);
        for b in replacements(prog, a) {
            let mut d = q.clone();
            d.atoms[i] = b.clone();
            let Ok(min) = minimize(prog, &[d], &root) else {
                continue;
            };
            let edit = (pattern(a, &vars), pattern(&b, &vars));
            out.push((edit, meaning(&min), min[0].clone()));
        }
    }
    out
}

fn leaves(prog: &Program) -> Vec<String> {
    let mut defs: BTreeMap<&str, (usize, bool)> = BTreeMap::new();
    let mut used: BTreeSet<&str> = BTreeSet::new();
    for c in &prog.concepts {
        let e = defs.entry(&c.head.rel).or_default();
        e.0 += 1;
        e.1 |= !c.plane.is_empty();
        for l in &c.body {
            if let Lit::Atom(a) = l {
                used.insert(&a.rel);
            }
        }
    }
    defs.into_iter()
        .filter(|(n, (k, planed))| *k == 1 && !planed && !used.contains(n))
        .map(|(n, _)| n.to_string())
        .collect()
}

/// Candidates ranked by support: (score, meaning, one definition, sources).
fn candidates(prog: &Program) -> Vec<(usize, Meaning, String, Vec<String>)> {
    let root = Plane::new();
    let names: BTreeSet<&str> = prog.concepts.iter().map(|c| c.head.rel.as_str()).collect();
    let mut known: BTreeMap<Meaning, &str> = BTreeMap::new();
    let mut single: Vec<(&str, Cq)> = Vec::new();
    for n in &names {
        let Ok(nf) = normal_form(prog, n, &root) else {
            continue;
        };
        known.entry(meaning(&nf)).or_insert(n);
        if nf.len() == 1 {
            single.push((n, nf[0].clone()));
        }
    }
    let all: Vec<(&str, Vec<Edited>)> = single.iter().map(|(n, q)| (*n, edits(prog, q))).collect();
    // Pairs A : C between existing concepts, per edit.
    let mut support: BTreeMap<&Edit, BTreeSet<(&str, &str)>> = BTreeMap::new();
    for (a, es) in &all {
        for (e, m, _) in es {
            if let Some(c) = known.get(m)
                && c != a
            {
                support.entry(e).or_default().insert((a, c));
            }
        }
    }
    let mut found: BTreeMap<&Meaning, (usize, &Cq, BTreeSet<String>)> = BTreeMap::new();
    for (b, es) in &all {
        for (e, m, q) in es {
            let Some(pairs) = support.get(e) else {
                continue;
            };
            if known.contains_key(m) {
                continue;
            }
            let entry = found.entry(m).or_insert((0, q, BTreeSet::new()));
            entry.0 += pairs.len();
            let (pa, pc) = pairs.iter().next().unwrap();
            entry.2.insert(format!("{pa} : {pc} :: {b} : D"));
        }
    }
    let mut out: Vec<(usize, Meaning, String, Vec<String>)> = found
        .into_iter()
        .map(|(m, (s, q, src))| (s, m.clone(), q.to_string(), src.into_iter().collect()))
        .collect();
    out.sort_by(|x, y| y.0.cmp(&x.0).then_with(|| x.1.cmp(&y.1)));
    out
}

fn main() {
    let src = std::fs::read_to_string("cases/kinship.agl").unwrap();
    let full = agl::parse(&src).unwrap();
    let root = Plane::new();
    let show = std::env::var("AGL_SHOW").is_ok();
    let held = leaves(&full);
    let mut hits = 0;
    for name in &held {
        let target = meaning(&normal_form(&full, name, &root).unwrap());
        let mut prog = full.clone();
        prog.concepts.retain(|c| c.head.rel != *name);
        let cands = candidates(&prog);
        let rank = cands.iter().position(|c| c.1 == target);
        let hit = rank.is_some_and(|r| r < TOP);
        hits += hit as usize;
        let place = rank.map_or("not proposed".to_string(), |r| format!("rank {}", r + 1));
        println!(
            "{} {name}: {place} of {}",
            if hit { "HIT " } else { "miss" },
            cands.len()
        );
        if show {
            for (s, _, def, srcs) in cands.iter().take(SHOWN) {
                println!("    {s:3}  {def}   ({})", srcs[0]);
            }
        }
    }
    println!(
        "{hits} of {} removed concepts in the top {TOP} (declared success: at least two thirds)",
        held.len()
    );
    println!("top candidates on the whole case, nothing removed:");
    for (s, _, def, srcs) in candidates(&full).iter().take(SHOWN) {
        println!("    {s:3}  {def}   ({})", srcs[0]);
    }
}

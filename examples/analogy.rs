//! Prototype outside the kernel (H51): noticing that something is missing
//! between two entities because a similar pair elsewhere has it.
//!
//! One reaction is removed from the glycolysis trunk. Every remaining
//! substrate-product pair (A, B) of a reaction is a base; every pair of
//! species (C, D) not yet joined by a reaction is a target. The target is
//! scored by the analogical proportion A : B :: C : D over ChEBI classes
//! (Miclet and Prade 2009): a class fits when the step from A to B gains or
//! loses it exactly as the step from C to D does. Classes are weighted by
//! rarity, so "chemical entity" counts for nothing. The best bases are
//! transferred as candidate inferences (Falkenhainer, Forbus, Gentner 1989):
//! the base reaction with A replaced by C and B by D, other participants
//! carried over unchanged. Each candidate is a surmise; the kernel then
//! checks it for balance of atoms and charge, and only balanced ones are
//! ranked.
//!
//!     cargo run --release --example analogy            # TPI and 5 random removals, seed 1
//!     cargo run --release --example analogy -- 7       # another seed
//!
//! Criterion declared before the run (docs/hypotheses.md, H51): the removed
//! reaction is among the top 3 balanced proposals. Result: 0 of 6, see
//! docs/review/2026-10-24-analogy.md. `AGL_SHOW=1` prints the best unchecked
//! proposals.

use std::collections::{BTreeMap, BTreeSet};

use agl::eval::evaluate;
use agl::model::{Plane, Term};
use agl::parse;
use agl::sim::Rng;

const TPI: &str = "RHEA_18585";
const TOP: usize = 3;
const RANDOM_REMOVALS: usize = 5;
/// Only the best proposals go to the kernel: checking thousands at once is slow.
const CHECKED: usize = 40;
/// Variant tried after the declared run failed (`true`); it ranked TPI lower
/// still, 2243 of 8100. Kept for reproduction, off by default.
const CHANGES_ONLY: bool = false;

/// Participants of a reaction: (species, side, coeff), sorted.
type Parts = Vec<(String, String, i64)>;

struct Trunk {
    metabolism: String,
    classes_src: String,
    balance_src: String,
    reactions: BTreeMap<String, Parts>,
    classes: BTreeMap<String, BTreeSet<String>>,
    names: BTreeMap<String, String>,
}

fn sym(t: &Term) -> String {
    match t {
        Term::Num(n, _) => format!("{}", *n as i64),
        other => other.to_string(),
    }
}

fn load() -> Trunk {
    let root = env!("CARGO_MANIFEST_DIR");
    let read = |p: &str| {
        std::fs::read_to_string(format!("{root}/{p}")).unwrap_or_else(|e| panic!("{p}: {e}"))
    };
    let metabolism = read("data/metabolism.agl");
    let classes_src = read("data/classes.agl");
    // Only the balance part of the trunk library: the pathway part names reactions.
    let lib = read("cases/trunk/lib.agl");
    let end = lib
        .find("\n# 2.")
        .expect("balance section of cases/trunk/lib.agl");
    let balance_src: String = lib[..end]
        .lines()
        .filter(|l| !l.trim_start().starts_with("include "))
        .map(|l| format!("{l}\n"))
        .collect();

    let prog = parse(&format!("{metabolism}\n{classes_src}")).expect("trunk parses");
    let mut reactions: BTreeMap<String, Parts> = BTreeMap::new();
    let mut classes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for f in &prog.facts {
        let arg = |role: &str| {
            f.atom
                .args
                .iter()
                .find(|(r, _)| r == role)
                .map(|(_, t)| sym(t))
                .unwrap()
        };
        match f.atom.rel.as_str() {
            "participates" => reactions.entry(arg("reaction")).or_default().push((
                arg("species"),
                arg("side"),
                arg("coeff").parse().unwrap(),
            )),
            "class_of" => {
                classes
                    .entry(arg("species"))
                    .or_default()
                    .insert(arg("class"));
            }
            _ => {}
        }
    }
    for parts in reactions.values_mut() {
        parts.sort();
    }
    let mut names = BTreeMap::new();
    for line in metabolism.lines().chain(classes_src.lines()) {
        if let Some(rest) = line.strip_prefix("# class ") {
            let (id, label) = rest.split_once(": ").unwrap();
            names.insert(id.to_string(), label.to_string());
        } else if let Some(rest) = line.strip_prefix("# CHEBI:")
            && let Some((head, _formula)) = rest.rsplit_once(": ")
            && let Some((id, label)) = head.split_once(' ')
        {
            names.insert(format!("CHEBI_{id}"), label.to_string());
        }
    }
    Trunk {
        metabolism,
        classes_src,
        balance_src,
        reactions,
        classes,
        names,
    }
}

/// Weight of a class: ln(N / species having it). A class every species has weighs 0.
fn weights(classes: &BTreeMap<String, BTreeSet<String>>) -> BTreeMap<String, f64> {
    let mut count: BTreeMap<&String, usize> = BTreeMap::new();
    for cs in classes.values() {
        for c in cs {
            *count.entry(c).or_default() += 1;
        }
    }
    let n = classes.len() as f64;
    count
        .into_iter()
        .map(|(c, k)| (c.clone(), (n / k as f64).ln()))
        .collect()
}

/// Weighted share of classes on which A : B :: C : D holds, among the classes
/// where the four are not all alike. Per class the proportion holds when
/// a - b = c - d (Boolean analogical proportion, Miclet and Prade 2009).
fn proportion(
    cl: &BTreeMap<String, BTreeSet<String>>,
    w: &BTreeMap<String, f64>,
    abcd: [&str; 4],
) -> f64 {
    let sets: Vec<&BTreeSet<String>> = abcd.iter().map(|s| &cl[*s]).collect();
    let all: BTreeSet<&String> = sets.iter().flat_map(|s| s.iter()).collect();
    let (mut fit, mut total) = (0.0, 0.0);
    for c in all {
        let v: Vec<i8> = sets.iter().map(|s| s.contains(c) as i8).collect();
        if v.iter().all(|x| *x == v[0]) {
            continue;
        }
        // Variant chosen after the declared run failed: count only classes that
        // change in the base or in the target, not context differences (a = b, c = d).
        if CHANGES_ONLY && v[0] == v[1] && v[2] == v[3] {
            continue;
        }
        total += w[c];
        if v[0] - v[1] == v[2] - v[3] {
            fit += w[c];
        }
    }
    if total == 0.0 { 0.0 } else { fit / total }
}

/// The same reaction read in either direction gets one name.
fn canonical(parts: &Parts) -> Parts {
    let mut flipped: Parts = parts
        .iter()
        .map(|(s, side, k)| {
            (
                s.clone(),
                if side == "left" { "right" } else { "left" }.to_string(),
                *k,
            )
        })
        .collect();
    flipped.sort();
    let mut p = parts.clone();
    p.sort();
    p.min(flipped)
}

struct Proposal {
    parts: Parts,
    score: f64,
    base: String,
    pair: [String; 4],
}

fn propose(t: &Trunk, removed: &str) -> Vec<Proposal> {
    let w = weights(&t.classes);
    let species: Vec<&String> = t.classes.keys().collect();
    let remaining: Vec<(&String, &Parts)> = t
        .reactions
        .iter()
        .filter(|(id, _)| id.as_str() != removed)
        .collect();
    let mut joined: BTreeSet<(&str, &str)> = BTreeSet::new();
    let mut existing: BTreeSet<Parts> = BTreeSet::new();
    for (_, parts) in &remaining {
        existing.insert(canonical(parts));
        for (x, sx, _) in parts.iter() {
            for (y, sy, _) in parts.iter() {
                if sx != sy {
                    joined.insert((x, y));
                }
            }
        }
    }
    let mut best: BTreeMap<Parts, Proposal> = BTreeMap::new();
    for (rid, parts) in &remaining {
        for (a, _, _) in parts.iter().filter(|p| p.1 == "left") {
            for (b, _, _) in parts.iter().filter(|p| p.1 == "right") {
                for c in &species {
                    for d in &species {
                        if c == d || joined.contains(&(c.as_str(), d.as_str())) {
                            continue;
                        }
                        if parts.iter().any(|(s, _, _)| s == *c || s == *d) {
                            continue;
                        }
                        let score = proportion(&t.classes, &w, [a, b, c, d]);
                        let mut new: Parts = parts
                            .iter()
                            .map(|(s, side, k)| {
                                let s = if s == a {
                                    (*c).clone()
                                } else if s == b {
                                    (*d).clone()
                                } else {
                                    s.clone()
                                };
                                (s, side.clone(), *k)
                            })
                            .collect();
                        new.sort();
                        let key = canonical(&new);
                        if existing.contains(&key) {
                            continue;
                        }
                        let better = best.get(&key).is_none_or(|p| score > p.score);
                        if better {
                            best.insert(
                                key,
                                Proposal {
                                    parts: new,
                                    score,
                                    base: (*rid).clone(),
                                    pair: [a.clone(), b.clone(), (*c).clone(), (*d).clone()],
                                },
                            );
                        }
                    }
                }
            }
        }
    }
    let mut out: Vec<Proposal> = best.into_values().collect();
    out.sort_by(|x, y| {
        y.score
            .total_cmp(&x.score)
            .then_with(|| canonical(&x.parts).cmp(&canonical(&y.parts)))
    });
    out
}

/// The kernel's verdict: which proposals are balanced in atoms and charge.
fn balanced(t: &Trunk, removed: &str, props: &[Proposal]) -> Vec<bool> {
    let tag = format!("({removed})");
    let tag2 = format!("reaction: {removed},");
    let kept: String = t
        .metabolism
        .lines()
        .filter(|l| !l.contains(&tag) && !l.contains(&tag2))
        .map(|l| format!("{l}\n"))
        .collect();
    let mut src = format!("{kept}\n{}\n{}\n", t.classes_src, t.balance_src);
    for (i, p) in props.iter().enumerate() {
        src.push_str(&format!(
            "fact cand_rx_{i}: reaction(id: cand_{i}) @ [llm_proposal]\n"
        ));
        for (k, (s, side, coeff)) in p.parts.iter().enumerate() {
            src.push_str(&format!(
                "fact cand_pa_{i}_{k}: participates(reaction: cand_{i}, species: {s}, side: {side}, coeff: {coeff}) @ [llm_proposal]\n"
            ));
        }
    }
    let prog = parse(&src).expect("fork parses");
    let out = evaluate(&prog, &Plane::new());
    assert!(!out.truncated, "closure truncated: raise the batch split");
    (0..props.len())
        .map(|i| {
            out.db
                .contains_key(&format!("balanced_all(reaction: cand_{i})"))
        })
        .collect()
}

fn name(t: &Trunk, id: &str) -> String {
    t.names.get(id).cloned().unwrap_or_else(|| id.to_string())
}

fn equation(t: &Trunk, parts: &Parts) -> String {
    let side = |s: &str| {
        parts
            .iter()
            .filter(|p| p.1 == s)
            .map(|(x, _, k)| {
                if *k == 1 {
                    name(t, x)
                } else {
                    format!("{k} {}", name(t, x))
                }
            })
            .collect::<Vec<_>>()
            .join(" + ")
    };
    format!("{} = {}", side("left"), side("right"))
}

/// Classes on which the proportion holds and that change between A and B: the reason, in words.
fn reason(t: &Trunk, w: &BTreeMap<String, f64>, pair: &[String; 4]) -> String {
    let [a, b, c, d] = pair.each_ref().map(|s| &t.classes[s]);
    let mut lost: Vec<(&String, f64)> = a
        .difference(b)
        .filter(|x| c.contains(*x) && !d.contains(*x))
        .map(|x| (x, w[x]))
        .collect();
    let mut gained: Vec<(&String, f64)> = b
        .difference(a)
        .filter(|x| d.contains(*x) && !c.contains(*x))
        .map(|x| (x, w[x]))
        .collect();
    for v in [&mut lost, &mut gained] {
        v.sort_by(|x, y| y.1.total_cmp(&x.1).then_with(|| x.0.cmp(y.0)));
        v.truncate(3);
    }
    let show = |v: &Vec<(&String, f64)>| {
        v.iter()
            .map(|(x, _)| name(t, x))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!("loses [{}], gains [{}]", show(&lost), show(&gained))
}

fn run(t: &Trunk, removed: &str) -> Option<usize> {
    let mut props = propose(t, removed);
    let total = props.len();
    let target = canonical(&t.reactions[removed]);
    if let Some(k) = props.iter().position(|p| canonical(&p.parts) == target) {
        let p = &props[k];
        println!(
            "(unchecked list: removed reaction at {} of {total}, score {:.3}, by {})",
            k + 1,
            p.score,
            p.base
        );
    }
    if std::env::var("AGL_SHOW").is_ok() {
        let w = weights(&t.classes);
        for p in props.iter().take(8) {
            println!(
                "   ? {:.3} {} | {}",
                p.score,
                equation(t, &p.parts),
                reason(t, &w, &p.pair)
            );
        }
    }
    props.truncate(CHECKED);
    let ok = balanced(t, removed, &props);
    let passed: Vec<&Proposal> = props
        .iter()
        .zip(&ok)
        .filter(|(_, b)| **b)
        .map(|(p, _)| p)
        .collect();
    let rank_raw = props.iter().position(|p| canonical(&p.parts) == target);
    let rank = passed.iter().position(|p| canonical(&p.parts) == target);
    println!(
        "## removed {removed}: {}",
        equation(t, &t.reactions[removed])
    );
    println!(
        "proposals: {total}, best {} checked, balanced by the kernel: {}; removed reaction ranks {} before the check, {} after",
        props.len(),
        passed.len(),
        rank_raw.map_or("—".to_string(), |r| (r + 1).to_string()),
        rank.map_or("—".to_string(), |r| (r + 1).to_string()),
    );
    let w = weights(&t.classes);
    for (i, p) in passed.iter().take(TOP).enumerate() {
        let mark = if canonical(&p.parts) == target {
            "  ← removed"
        } else {
            ""
        };
        println!(
            "  {}. {:.3}  {}{mark}",
            i + 1,
            p.score,
            equation(t, &p.parts)
        );
        println!(
            "     by {}: {} : {} :: {} : {}; {}",
            p.base,
            name(t, &p.pair[0]),
            name(t, &p.pair[1]),
            name(t, &p.pair[2]),
            name(t, &p.pair[3]),
            reason(t, &w, &p.pair)
        );
    }
    println!();
    rank
}

fn main() {
    let seed: u64 = std::env::args()
        .nth(1)
        .map_or(1, |s| s.parse().expect("seed is a number"));
    let t = load();
    let mut removals = vec![TPI.to_string()];
    let mut others: Vec<String> = t
        .reactions
        .keys()
        .filter(|k| k.as_str() != TPI)
        .cloned()
        .collect();
    let mut rng = Rng::new(seed);
    for _ in 0..RANDOM_REMOVALS.min(others.len()) {
        removals.push(others.remove(rng.below(others.len())));
    }
    let mut hits = 0;
    for r in &removals {
        if run(&t, r).is_some_and(|k| k < TOP) {
            hits += 1;
        }
    }
    println!(
        "found in top {TOP}: {hits} of {} (seed {seed})",
        removals.len()
    );
}

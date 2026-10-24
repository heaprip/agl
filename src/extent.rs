//! Where a statement holds, and what goes with what across planes (H52).
//!
//! In a topos the truth value of a statement is the region where it holds,
//! not yes or no. `extents` answers "where does p hold" over every context
//! the contradiction scan visits: the planes in use and all their
//! intersections, plus the root. The answer is exact for every plane: what is
//! visible in a plane depends only on the planes in use that contain it, and
//! the widest plane with the same set is one of these contexts
//! (docs/review/2026-10-24-sheaves.md, item 2).
//!
//! `implications` reads the evaluated contexts as a formal context (Wille
//! 1982): objects are a context with the values of the roles, attributes are
//! relations over the same roles. An implication A → B holds when every
//! object with A has B. Single-premise implications are shown without the
//! ones that follow by transitivity; near implications name their exceptions
//! and the contexts they sit in.

use std::collections::{BTreeMap, BTreeSet};

use crate::check::{Evals, contexts};
use crate::model::*;

/// Implications that fail on more objects than this share are not shown.
const MIN_CONFIDENCE: f64 = 0.75;
/// Near implications need at least this many objects with the premise.
const MIN_SUPPORT: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Holds {
    Yes,
    No,
    Conflict,
}

/// A ground atom and the contexts where it holds, its negation holds, or the
/// two are in conflict. Contexts not listed answer `unknown`.
pub struct Extent {
    pub atom: String,
    pub by_context: Vec<(Plane, Holds)>,
}

/// Every context worth evaluating, with the root, and whether the closure of
/// intersections was complete.
fn all_contexts(prog: &Program) -> (Vec<Plane>, bool) {
    let (mut cs, complete) = contexts(prog);
    if !cs.contains(&Plane::new()) {
        cs.push(Plane::new());
    }
    cs.sort_by_key(plane_to_string);
    (cs, complete)
}

fn matches(pat: &Atom, ground: &Atom) -> bool {
    if pat.rel != ground.rel {
        return false;
    }
    let mut bound: BTreeMap<&str, String> = BTreeMap::new();
    pat.args.iter().all(|(role, t)| {
        let Some((_, g)) = ground.args.iter().find(|(r, _)| r == role) else {
            return false;
        };
        let g = g.to_string();
        match t {
            Term::Var(v) => match bound.get(v.as_str()) {
                Some(b) => *b == g,
                None => {
                    bound.insert(v, g);
                    true
                }
            },
            other => other.to_string() == g,
        }
    })
}

pub fn extents(prog: &Program, pattern: &Atom) -> (Vec<Extent>, bool) {
    let (contexts, complete) = all_contexts(prog);
    let mut evals = Evals::new(prog);
    let pos = Atom {
        neg: false,
        ..pattern.clone()
    };
    let mut found: BTreeMap<String, Vec<(Plane, Holds)>> = BTreeMap::new();
    for ctx in &contexts {
        let out = evals.get(ctx);
        let mut here: BTreeMap<String, Holds> = BTreeMap::new();
        for (atom, _) in out.db.values() {
            let a = Atom {
                neg: false,
                ..atom.clone()
            };
            if matches(&pos, &a) {
                let h = if atom.neg { Holds::No } else { Holds::Yes };
                here.insert(a.key(), h);
            }
        }
        for key in out.conflicts.keys() {
            if let Ok(a) = crate::parse::parse_atom_in(key, &prog.units)
                && matches(&pos, &a)
            {
                here.insert(a.key(), Holds::Conflict);
            }
        }
        for (k, h) in here {
            found.entry(k).or_default().push((ctx.clone(), h));
        }
    }
    let out = found
        .into_iter()
        .map(|(atom, by_context)| Extent { atom, by_context })
        .collect();
    (out, complete)
}

pub fn render_extents(exts: &[Extent], complete: bool) -> String {
    let mut s = String::new();
    if !complete {
        s.push_str("warning: plane intersections were cut off; the answer is partial\n");
    }
    if exts.is_empty() {
        s.push_str("holds nowhere, and its negation nowhere\n");
    }
    for e in exts {
        s.push_str(&format!("{}\n", e.atom));
        for (h, word) in [
            (Holds::Yes, "yes"),
            (Holds::No, "no"),
            (Holds::Conflict, "conflict"),
        ] {
            let planes: Vec<String> = e
                .by_context
                .iter()
                .filter(|(_, x)| *x == h)
                .map(|(p, _)| plane_to_string(p))
                .collect();
            if !planes.is_empty() {
                s.push_str(&format!("  {word}: {}\n", planes.join(", ")));
            }
        }
    }
    s
}

/// A context and the values of the roles, in role order.
pub type Object = (String, String);

pub struct Implication {
    /// Relations with the same objects, the premise first.
    pub premise: Vec<String>,
    pub conclusion: Vec<String>,
    /// Objects with the premise.
    pub support: usize,
    /// Objects with the premise and without the conclusion.
    pub exceptions: Vec<Object>,
}

pub struct Implications {
    /// Role signature and the classes of relations with the same objects.
    pub signatures: Vec<(String, Vec<Vec<String>>)>,
    pub exact: Vec<Implication>,
    pub near: Vec<Implication>,
    pub complete: bool,
}

/// Role signature → relation → objects, over every evaluated context, and
/// whether the closure of intersections was complete.
pub type Table = BTreeMap<String, BTreeMap<String, BTreeSet<Object>>>;

pub fn table(prog: &Program) -> (Table, bool) {
    let (contexts, complete) = all_contexts(prog);
    let mut evals = Evals::new(prog);
    let mut table: Table = BTreeMap::new();
    for ctx in &contexts {
        let name = plane_to_string(ctx);
        let out = evals.get(ctx);
        for (atom, _) in out.db.values().filter(|(a, _)| !a.neg) {
            let roles: Vec<&str> = atom.args.iter().map(|(r, _)| r.as_str()).collect();
            let values: Vec<String> = atom.args.iter().map(|(r, t)| format!("{r}: {t}")).collect();
            table
                .entry(roles.join(", "))
                .or_default()
                .entry(atom.rel.clone())
                .or_default()
                .insert((name.clone(), values.join(", ")));
        }
        // An outcome is not needed again: keep memory flat over many contexts.
        evals.done.clear();
    }
    (table, complete)
}

pub fn implications(prog: &Program) -> Implications {
    let (table, complete) = table(prog);
    let mut res = Implications {
        signatures: vec![],
        exact: vec![],
        near: vec![],
        complete,
    };
    for (sig, rels) in table {
        if rels.len() < 2 {
            continue;
        }
        // Relations with the same objects form one attribute.
        let mut classes: BTreeMap<&BTreeSet<Object>, Vec<String>> = BTreeMap::new();
        for (rel, objs) in &rels {
            classes.entry(objs).or_default().push(rel.clone());
        }
        let classes: Vec<(&BTreeSet<Object>, Vec<String>)> = classes.into_iter().collect();
        let n = classes.len();
        let below = |i: usize, j: usize| i != j && classes[i].0.is_subset(classes[j].0);
        for i in 0..n {
            for j in 0..n {
                if !below(i, j) {
                    continue;
                }
                // Only covering pairs: the rest follow by transitivity.
                if (0..n).any(|k| below(i, k) && below(k, j)) {
                    continue;
                }
                res.exact.push(Implication {
                    premise: classes[i].1.clone(),
                    conclusion: classes[j].1.clone(),
                    support: classes[i].0.len(),
                    exceptions: vec![],
                });
            }
        }
        for i in 0..n {
            for j in 0..n {
                if i == j || below(i, j) {
                    continue;
                }
                let (a, b) = (classes[i].0, classes[j].0);
                let exceptions: Vec<Object> = a.difference(b).cloned().collect();
                let confidence = 1.0 - exceptions.len() as f64 / a.len() as f64;
                if a.len() >= MIN_SUPPORT && confidence >= MIN_CONFIDENCE {
                    res.near.push(Implication {
                        premise: classes[i].1.clone(),
                        conclusion: classes[j].1.clone(),
                        support: a.len(),
                        exceptions,
                    });
                }
            }
        }
        let groups = classes
            .into_iter()
            .map(|(_, names)| names)
            .filter(|names| names.len() > 1)
            .collect();
        res.signatures.push((sig, groups));
    }
    res
}

pub fn render_implications(imp: &Implications) -> String {
    let mut s = String::new();
    if !imp.complete {
        s.push_str("warning: plane intersections were cut off; the table is partial\n");
    }
    s.push_str("same objects in every context:\n");
    for (sig, groups) in &imp.signatures {
        for g in groups {
            s.push_str(&format!("  ({sig}) {}\n", g.join(" = ")));
        }
    }
    s.push_str("implications that hold in every context:\n");
    for i in &imp.exact {
        s.push_str(&format!(
            "  {} → {}  ({} objects)\n",
            i.premise[0], i.conclusion[0], i.support
        ));
    }
    s.push_str(&format!(
        "near implications (at least {} objects, {}% hold):\n",
        MIN_SUPPORT,
        (MIN_CONFIDENCE * 100.0) as usize
    ));
    for i in &imp.near {
        s.push_str(&format!(
            "  {} → {}  fails on {} of {}:\n",
            i.premise[0],
            i.conclusion[0],
            i.exceptions.len(),
            i.support
        ));
        let mut by_ctx: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for (ctx, obj) in &i.exceptions {
            by_ctx.entry(ctx).or_default().push(obj);
        }
        for (ctx, objs) in by_ctx {
            s.push_str(&format!("    in {ctx}: {}\n", objs.join("; ")));
        }
    }
    s
}

//! Evaluation of a program in a context plane.
//!
//! A fact or rule is visible in context `c` when `c` lies within its plane;
//! this gives inheritance down nested planes. Evaluation is a naive fixpoint
//! that may derive both `p` and `¬p`; conflicts are then resolved:
//! strict beats defeasible, then a declared `defeats`, then the more specific
//! plane. Losers are blocked and the fixpoint is recomputed without them.
//! Unresolved and strict-vs-strict conflicts block both sides and are reported.

use std::collections::{BTreeMap, BTreeSet};

use crate::model::*;

/// Upper bound on derived atoms, against runaway arithmetic recursion.
const MAX_ATOMS: usize = 100_000;

#[derive(Clone, Debug)]
pub struct Derivation {
    pub source: String,
    pub is_fact: bool,
    pub strict: bool,
    pub plane: Plane,
    pub premises: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConflictKind {
    /// Both sides strict: a real contradiction.
    Hard,
    /// Both defeasible with no priority and no specificity: localized conflict.
    Unresolved,
}

#[derive(Clone, Debug)]
pub struct Conflict {
    pub positive: String,
    pub kind: ConflictKind,
    pub sources_pos: Vec<String>,
    pub sources_neg: Vec<String>,
}

#[derive(Default, Debug)]
pub struct Outcome {
    pub db: BTreeMap<String, (Atom, Vec<Derivation>)>,
    pub conflicts: BTreeMap<String, Conflict>,
    /// loser key -> reason
    pub defeated: BTreeMap<String, String>,
    pub truncated: bool,
}

pub fn evaluate(prog: &Program, ctx: &Plane) -> Outcome {
    let facts: Vec<&Fact> = prog
        .facts
        .iter()
        .filter(|f| prog.axes.plane_within(ctx, &f.plane))
        .collect();
    let rules: Vec<&Rule> = prog
        .rules
        .iter()
        .filter(|r| prog.axes.plane_within(ctx, &r.plane))
        .collect();
    let mut out = Outcome::default();
    let mut blocked: BTreeSet<String> = BTreeSet::new();
    loop {
        let (db, truncated) = closure(&facts, &rules, &blocked);
        out.truncated |= truncated;
        let mut newly = Vec::new();
        for (key, (atom, derivs)) in &db {
            if atom.neg {
                continue;
            }
            let ckey = atom.complement().key();
            let Some((_, cderivs)) = db.get(&ckey) else {
                continue;
            };
            match resolve(prog, derivs, cderivs) {
                Winner::Pos => {
                    out.defeated.insert(
                        ckey.clone(),
                        format!("defeated by {}", sources(derivs).join(", ")),
                    );
                    newly.push(ckey);
                }
                Winner::Neg => {
                    out.defeated.insert(
                        key.clone(),
                        format!("defeated by {}", sources(cderivs).join(", ")),
                    );
                    newly.push(key.clone());
                }
                Winner::None(kind) => {
                    out.conflicts.insert(
                        key.clone(),
                        Conflict {
                            positive: key.clone(),
                            kind,
                            sources_pos: sources(derivs),
                            sources_neg: sources(cderivs),
                        },
                    );
                    newly.push(key.clone());
                    newly.push(ckey);
                }
            }
        }
        let before = blocked.len();
        blocked.extend(newly);
        if blocked.len() == before {
            out.db = db;
            return out;
        }
    }
}

fn sources(derivs: &[Derivation]) -> Vec<String> {
    let mut s: Vec<String> = derivs.iter().map(|d| d.source.clone()).collect();
    s.sort();
    s.dedup();
    s
}

enum Winner {
    Pos,
    Neg,
    None(ConflictKind),
}

fn resolve(prog: &Program, pos: &[Derivation], neg: &[Derivation]) -> Winner {
    let ps = pos.iter().any(|d| d.strict);
    let ns = neg.iter().any(|d| d.strict);
    match (ps, ns) {
        (true, true) => return Winner::None(ConflictKind::Hard),
        (true, false) => return Winner::Pos,
        (false, true) => return Winner::Neg,
        (false, false) => {}
    }
    let beats = |a: &[Derivation], b: &[Derivation]| {
        a.iter().any(|x| {
            b.iter()
                .any(|y| prog.defeats.contains(&(x.source.clone(), y.source.clone())))
        })
    };
    match (beats(pos, neg), beats(neg, pos)) {
        (true, false) => return Winner::Pos,
        (false, true) => return Winner::Neg,
        _ => {}
    }
    let more_specific = |a: &[Derivation], b: &[Derivation]| {
        a.iter().any(|x| {
            b.iter()
                .all(|y| prog.axes.strictly_within(&x.plane, &y.plane))
        })
    };
    match (more_specific(pos, neg), more_specific(neg, pos)) {
        (true, false) => Winner::Pos,
        (false, true) => Winner::Neg,
        _ => Winner::None(ConflictKind::Unresolved),
    }
}

type Db = BTreeMap<String, (Atom, Vec<Derivation>)>;

fn closure(facts: &[&Fact], rules: &[&Rule], blocked: &BTreeSet<String>) -> (Db, bool) {
    let mut db: Db = BTreeMap::new();
    for f in facts {
        let key = f.atom.key();
        if blocked.contains(&key) {
            continue;
        }
        let d = Derivation {
            source: f.id.clone(),
            is_fact: true,
            strict: true,
            plane: f.plane.clone(),
            premises: vec![],
        };
        db.entry(key)
            .or_insert_with(|| (f.atom.clone(), vec![]))
            .1
            .push(d);
    }
    loop {
        let mut added = false;
        let mut by_rel: BTreeMap<(&str, bool), Vec<String>> = BTreeMap::new();
        for (k, (a, _)) in &db {
            by_rel
                .entry((a.rel.as_str(), a.neg))
                .or_default()
                .push(k.clone());
        }
        let mut new: Vec<(Atom, Derivation)> = Vec::new();
        for r in rules {
            let mut matches = Vec::new();
            match_body(
                &r.body,
                0,
                &mut BTreeMap::new(),
                &mut Vec::new(),
                &db,
                &by_rel,
                &mut matches,
            );
            for (binding, mut premises) in matches {
                // A body is a conjunction: its premises form a set, not a sequence.
                premises.sort();
                premises.dedup();
                let head = subst(&r.head, &binding);
                if !head.is_ground() {
                    continue;
                }
                let strict = r.strength == Strength::Strict
                    && premises
                        .iter()
                        .all(|p| db.get(p).is_some_and(|(_, ds)| ds.iter().any(|d| d.strict)));
                new.push((
                    head,
                    Derivation {
                        source: r.id.clone(),
                        is_fact: false,
                        strict,
                        plane: r.plane.clone(),
                        premises,
                    },
                ));
            }
        }
        for (head, d) in new {
            let key = head.key();
            if blocked.contains(&key) {
                continue;
            }
            let entry = db.entry(key).or_insert_with(|| (head, vec![]));
            if !entry
                .1
                .iter()
                .any(|x| x.source == d.source && x.premises == d.premises)
            {
                entry.1.push(d);
                added = true;
            }
        }
        if db.len() > MAX_ATOMS {
            return (db, true);
        }
        if !added {
            return (db, false);
        }
    }
}

fn match_body(
    lits: &[Lit],
    i: usize,
    binding: &mut BTreeMap<String, Term>,
    premises: &mut Vec<String>,
    db: &Db,
    by_rel: &BTreeMap<(&str, bool), Vec<String>>,
    out: &mut Vec<(BTreeMap<String, Term>, Vec<String>)>,
) {
    if i == lits.len() {
        out.push((binding.clone(), premises.clone()));
        return;
    }
    match &lits[i] {
        Lit::Atom(pat) => {
            let Some(keys) = by_rel.get(&(pat.rel.as_str(), pat.neg)) else {
                return;
            };
            for k in keys {
                let (ground, _) = &db[k];
                let mut b = binding.clone();
                if unify(pat, ground, &mut b) {
                    premises.push(k.clone());
                    match_body(lits, i + 1, &mut b, premises, db, by_rel, out);
                    premises.pop();
                }
            }
        }
        Lit::Cmp(l, op, r) => {
            if *op == CmpOp::Eq
                && let Expr::Term(Term::Var(v)) = l
                && !binding.contains_key(v)
            {
                if let Some(val) = eval_expr(r, binding) {
                    binding.insert(v.clone(), val);
                    match_body(lits, i + 1, binding, premises, db, by_rel, out);
                    binding.remove(v);
                }
                return;
            }
            if compare(l, *op, r, binding) == Some(true) {
                match_body(lits, i + 1, binding, premises, db, by_rel, out);
            }
        }
    }
}

/// Pattern roles must all be present in the ground atom; the atom may have more.
fn unify(pat: &Atom, ground: &Atom, b: &mut BTreeMap<String, Term>) -> bool {
    for (role, pt) in &pat.args {
        let Some((_, gt)) = ground.args.iter().find(|(r, _)| r == role) else {
            return false;
        };
        match pt {
            Term::Var(v) => match b.get(v) {
                Some(bound) if !term_eq(bound, gt) => return false,
                Some(_) => {}
                None => {
                    b.insert(v.clone(), gt.clone());
                }
            },
            t if !term_eq(t, gt) => return false,
            _ => {}
        }
    }
    true
}

fn term_eq(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Num(x), Term::Num(y)) => (x - y).abs() <= 1e-12 * x.abs().max(y.abs()).max(1.0),
        _ => a == b,
    }
}

pub fn subst(a: &Atom, b: &BTreeMap<String, Term>) -> Atom {
    let args = a
        .args
        .iter()
        .map(|(r, t)| {
            let t = match t {
                Term::Var(v) => b.get(v).cloned().unwrap_or_else(|| t.clone()),
                _ => t.clone(),
            };
            (r.clone(), t)
        })
        .collect();
    Atom {
        rel: a.rel.clone(),
        args,
        neg: a.neg,
    }
}

fn eval_expr(e: &Expr, b: &BTreeMap<String, Term>) -> Option<Term> {
    match e {
        Expr::Term(Term::Var(v)) => b.get(v).cloned(),
        Expr::Term(t) => Some(t.clone()),
        Expr::Bin(l, op, r) => {
            let (Term::Num(x), Term::Num(y)) = (eval_expr(l, b)?, eval_expr(r, b)?) else {
                return None;
            };
            let v = match op {
                '+' => x + y,
                '-' => x - y,
                '*' => x * y,
                '/' if y != 0.0 => x / y,
                // Integer powers stay bit-identical across platforms; `powf` goes through libm.
                '^' if y.fract() == 0.0 && y.abs() <= i32::MAX as f64 => x.powi(y as i32),
                '^' => x.powf(y),
                _ => return None,
            };
            Some(Term::Num(v))
        }
    }
}

fn compare(l: &Expr, op: CmpOp, r: &Expr, b: &BTreeMap<String, Term>) -> Option<bool> {
    let (x, y) = (eval_expr(l, b)?, eval_expr(r, b)?);
    match (&x, &y) {
        (Term::Num(a), Term::Num(c)) => Some(match op {
            CmpOp::Lt => a < c,
            CmpOp::Le => a <= c,
            CmpOp::Gt => a > c,
            CmpOp::Ge => a >= c,
            CmpOp::Eq => term_eq(&x, &y),
            CmpOp::Ne => !term_eq(&x, &y),
        }),
        _ => match op {
            CmpOp::Eq => Some(x == y),
            CmpOp::Ne => Some(x != y),
            _ => None,
        },
    }
}

/// Human-readable grounds of a derived atom, as an indented tree.
pub fn explain(out: &Outcome, key: &str) -> String {
    let mut s = String::new();
    explain_rec(out, key, 0, &mut BTreeSet::new(), &mut s);
    s
}

/// The derivation shown in explanations, chosen independently of insertion
/// order: strict first, then facts, then by source and premises.
fn canonical(derivs: &[Derivation]) -> &Derivation {
    derivs
        .iter()
        .min_by(|a, b| {
            (!a.strict, !a.is_fact, &a.source, &a.premises).cmp(&(
                !b.strict,
                !b.is_fact,
                &b.source,
                &b.premises,
            ))
        })
        .expect("a derived atom has at least one derivation")
}

fn explain_rec(
    out: &Outcome,
    key: &str,
    depth: usize,
    seen: &mut BTreeSet<String>,
    s: &mut String,
) {
    let pad = "  ".repeat(depth);
    let Some((_, derivs)) = out.db.get(key) else {
        s.push_str(&format!("{pad}{key}  (not derived)\n"));
        return;
    };
    let d = canonical(derivs);
    let kind = if d.is_fact {
        "fact"
    } else if d.strict {
        "strict"
    } else {
        "defeasible"
    };
    s.push_str(&format!(
        "{pad}{key}  ← {} [{kind}] @ {}\n",
        d.source,
        plane_to_string(&d.plane)
    ));
    if !seen.insert(key.to_string()) || depth > 12 {
        return;
    }
    for p in &d.premises {
        explain_rec(out, p, depth + 1, seen, s);
    }
}

//! Evaluation of a program in a context plane.
//!
//! A fact or rule is visible in context `c` when `c` lies within its plane;
//! this gives inheritance down nested planes. Evaluation is a naive fixpoint,
//! stratum by stratum (an aggregate needs its relations complete), that may
//! derive both `p` and `¬p`; conflicts are then resolved: strict beats
//! defeasible, then a declared `defeats`, then the more specific plane. Losers
//! are blocked and the fixpoint is recomputed without them. Unresolved and
//! strict-vs-strict conflicts block both sides and are reported, as are
//! violations of `unique` declarations.

use std::collections::{BTreeMap, BTreeSet};

use crate::model::*;
use crate::units::Dim;

/// Prefix of a premise that records an aggregate which found nothing.
pub const ABSENT: &str = "∅ ";

/// Upper bound on derived atoms, against runaway arithmetic recursion.
const MAX_ATOMS: usize = 100_000;

#[derive(Clone, Debug)]
pub struct Derivation {
    pub source: String,
    pub is_fact: bool,
    pub strict: bool,
    pub plane: Plane,
    pub premises: Vec<String>,
    /// Trust: a fact's status rank; for a rule, its weakest premise.
    pub rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConflictKind {
    /// Both sides strict: a real contradiction.
    Hard,
    /// Both defeasible with no priority and no specificity: localized conflict.
    Unresolved,
    /// Two values where a `unique` declaration allows one.
    Uniqueness,
    /// A derived atom matches a `forbid` constraint.
    Violation,
}

#[derive(Clone, Debug)]
pub struct Conflict {
    pub positive: String,
    pub kind: ConflictKind,
    pub sources_pos: Vec<String>,
    pub sources_neg: Vec<String>,
    /// The least trusted facts it rests on, as `id [status]`, when statuses differ.
    pub blame: Vec<String>,
}

#[derive(Default, Debug)]
pub struct Outcome {
    pub db: BTreeMap<String, (Atom, Vec<Derivation>)>,
    pub conflicts: BTreeMap<String, Conflict>,
    /// loser key -> reason
    pub defeated: BTreeMap<String, String>,
    /// Evaluation errors, such as adding quantities of different dimensions.
    pub errors: BTreeSet<String>,
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
    let (strata, _) = strata(&prog.rules);
    let top = prog.status_rank.values().copied().max().unwrap_or(0);
    let mut out = Outcome::default();
    let mut blocked: BTreeSet<String> = BTreeSet::new();
    loop {
        let (db, truncated) = closure(
            prog,
            &facts,
            &rules,
            &strata,
            &blocked,
            top,
            &mut out.errors,
        );
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
                            blame: vec![],
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
            check_uniques(prog, &db, &mut out.conflicts);
            check_forbids(prog, ctx, &db, &mut out.conflicts);
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

fn best_rank(derivs: &[Derivation]) -> usize {
    derivs.iter().map(|d| d.rank).max().unwrap_or(0)
}

fn resolve(prog: &Program, pos: &[Derivation], neg: &[Derivation]) -> Winner {
    let ps = pos.iter().any(|d| d.strict);
    let ns = neg.iter().any(|d| d.strict);
    // Between two sides of the same strength, the more trusted one wins: an
    // LLM proposal against a textbook is a rejected candidate, not a
    // contradiction. Only derivations of the deciding strength count, so a
    // defeasible derivation cannot lend its trust to a strict one.
    let rank_of = |ds: &[Derivation], strict: bool| {
        ds.iter()
            .filter(|d| d.strict == strict)
            .map(|d| d.rank)
            .max()
            .unwrap_or(0)
    };
    let by_rank = |strict: bool| match rank_of(pos, strict).cmp(&rank_of(neg, strict)) {
        std::cmp::Ordering::Greater => Some(Winner::Pos),
        std::cmp::Ordering::Less => Some(Winner::Neg),
        std::cmp::Ordering::Equal => None,
    };
    match (ps, ns) {
        (true, true) => return by_rank(true).unwrap_or(Winner::None(ConflictKind::Hard)),
        (true, false) => return Winner::Pos,
        (false, true) => return Winner::Neg,
        (false, false) => {
            if let Some(w) = by_rank(false) {
                return w;
            }
        }
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

/// Stratum of every derived relation: a head sits at or above its body
/// relations and strictly above the relations it aggregates over. Returns the
/// relations caught in a cycle through an aggregate, which cannot be
/// stratified.
pub fn strata(rules: &[Rule]) -> (BTreeMap<String, usize>, Vec<String>) {
    let mut level: BTreeMap<String, usize> = BTreeMap::new();
    let limit = rules.len() + 1;
    for round in 0..=limit {
        let mut changed = false;
        for r in rules {
            let mut need = 0;
            for lit in &r.body {
                match lit {
                    Lit::Atom(a) => need = need.max(level.get(&a.rel).copied().unwrap_or(0)),
                    Lit::Agg { over, .. } => {
                        for a in over {
                            need = need.max(level.get(&a.rel).copied().unwrap_or(0) + 1);
                        }
                    }
                    Lit::Cmp(..) => {}
                }
            }
            let cur = level.entry(r.head.rel.clone()).or_insert(0);
            if need > *cur && need <= limit {
                *cur = need;
                changed = true;
            }
        }
        if !changed {
            return (level, vec![]);
        }
        if round == limit {
            break;
        }
    }
    let cyclic = level
        .iter()
        .filter(|(_, l)| **l >= limit)
        .map(|(r, _)| r.clone())
        .collect();
    (level, cyclic)
}

type Db = BTreeMap<String, (Atom, Vec<Derivation>)>;
type Binding = BTreeMap<String, Term>;

fn closure(
    prog: &Program,
    facts: &[&Fact],
    rules: &[&Rule],
    strata: &BTreeMap<String, usize>,
    blocked: &BTreeSet<String>,
    top: usize,
    errors: &mut BTreeSet<String>,
) -> (Db, bool) {
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
            rank: prog.status_rank.get(&f.status).copied().unwrap_or(0),
        };
        db.entry(key)
            .or_insert_with(|| (f.atom.clone(), vec![]))
            .1
            .push(d);
    }
    let mut levels: Vec<usize> = rules
        .iter()
        .map(|r| strata.get(&r.head.rel).copied().unwrap_or(0))
        .collect();
    levels.sort();
    levels.dedup();
    for level in levels {
        let layer: Vec<&Rule> = rules
            .iter()
            .copied()
            .filter(|r| strata.get(&r.head.rel).copied().unwrap_or(0) == level)
            .collect();
        if fixpoint(&mut db, &layer, blocked, top, errors) {
            return (db, true);
        }
    }
    (db, false)
}

/// Saturates `db` with one stratum of rules; returns true if truncated.
fn fixpoint(
    db: &mut Db,
    rules: &[&Rule],
    blocked: &BTreeSet<String>,
    top: usize,
    errors: &mut BTreeSet<String>,
) -> bool {
    loop {
        let mut added = false;
        let index = index_by_rel(db);
        let mut new: Vec<(Atom, Derivation)> = Vec::new();
        for r in rules {
            let mut matches = Vec::new();
            let mut ctx = Matcher {
                db,
                index: &index,
                rule: &r.id,
                errors: &mut *errors,
            };
            let body = schedule(r);
            ctx.body(&body, 0, &mut Binding::new(), &mut Vec::new(), &mut matches);
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
                        .filter(|p| !p.starts_with(ABSENT))
                        .all(|p| db.get(p).is_some_and(|(_, ds)| ds.iter().any(|d| d.strict)));
                let rank = premises
                    .iter()
                    .filter(|p| !p.starts_with(ABSENT))
                    .map(|p| db.get(p).map_or(0, |(_, ds)| best_rank(ds)))
                    .min()
                    .unwrap_or(top);
                new.push((
                    head,
                    Derivation {
                        source: r.id.clone(),
                        is_fact: false,
                        strict,
                        plane: r.plane.clone(),
                        premises,
                        rank,
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
            return true;
        }
        if !added {
            return false;
        }
    }
}

fn expr_vars(e: &Expr, out: &mut BTreeSet<String>) {
    match e {
        Expr::Term(Term::Var(v)) => {
            out.insert(v.clone());
        }
        Expr::Term(_) => {}
        Expr::Bin(l, _, r) => {
            expr_vars(l, out);
            expr_vars(r, out);
        }
    }
}

/// Variables a literal mentions where the rest of the rule can see them. An
/// aggregate's `over` variables are local; only its result is visible.
fn visible_vars(lit: &Lit, out: &mut BTreeSet<String>) {
    match lit {
        Lit::Atom(a) => out.extend(a.vars().map(str::to_string)),
        Lit::Cmp(l, _, r) => {
            expr_vars(l, out);
            expr_vars(r, out);
        }
        Lit::Agg { var, .. } => {
            out.insert(var.clone());
        }
    }
}

/// Orders a rule body so that the result does not depend on how it was
/// written. Atoms run first. A comparison runs once its variables are bound,
/// and `?v = expr` binds `?v`. An aggregate runs once its grouping variables
/// are bound: the variables it shares with the head and the other literals.
fn schedule(r: &Rule) -> Vec<Lit> {
    let mut order: Vec<Lit> = Vec::new();
    let mut bound: BTreeSet<String> = BTreeSet::new();
    let mut pending: Vec<usize> = Vec::new();
    for (i, lit) in r.body.iter().enumerate() {
        if let Lit::Atom(a) = lit {
            bound.extend(a.vars().map(str::to_string));
            order.push(lit.clone());
        } else {
            pending.push(i);
        }
    }
    let requirement = |i: usize, bound: &BTreeSet<String>| -> (BTreeSet<String>, Option<String>) {
        match &r.body[i] {
            Lit::Cmp(Expr::Term(Term::Var(v)), CmpOp::Eq, rhs) if !bound.contains(v) => {
                let mut need = BTreeSet::new();
                expr_vars(rhs, &mut need);
                (need, Some(v.clone()))
            }
            Lit::Cmp(l, _, rhs) => {
                let mut need = BTreeSet::new();
                expr_vars(l, &mut need);
                expr_vars(rhs, &mut need);
                (need, None)
            }
            Lit::Agg {
                var, expr, over, ..
            } => {
                let mut inner = BTreeSet::new();
                expr_vars(expr, &mut inner);
                over.iter()
                    .for_each(|a| inner.extend(a.vars().map(str::to_string)));
                let mut outer: BTreeSet<String> = r.head.vars().map(str::to_string).collect();
                for (j, other) in r.body.iter().enumerate() {
                    if j != i {
                        visible_vars(other, &mut outer);
                    }
                }
                (
                    inner.intersection(&outer).cloned().collect(),
                    Some(var.clone()),
                )
            }
            Lit::Atom(_) => (BTreeSet::new(), None),
        }
    };
    while !pending.is_empty() {
        let ready = pending
            .iter()
            .position(|&i| requirement(i, &bound).0.is_subset(&bound));
        let Some(p) = ready else {
            // Nothing is ready: the remaining literals cannot match.
            order.extend(pending.iter().map(|&i| r.body[i].clone()));
            break;
        };
        let i = pending.remove(p);
        if let (_, Some(v)) = requirement(i, &bound) {
            bound.insert(v);
        }
        order.push(r.body[i].clone());
    }
    order
}

fn index_by_rel(db: &Db) -> BTreeMap<(String, bool), Vec<String>> {
    let mut index: BTreeMap<(String, bool), Vec<String>> = BTreeMap::new();
    for (k, (a, _)) in db {
        index
            .entry((a.rel.clone(), a.neg))
            .or_default()
            .push(k.clone());
    }
    index
}

struct Matcher<'a> {
    db: &'a Db,
    index: &'a BTreeMap<(String, bool), Vec<String>>,
    rule: &'a str,
    errors: &'a mut BTreeSet<String>,
}

impl Matcher<'_> {
    fn body(
        &mut self,
        lits: &[Lit],
        i: usize,
        binding: &mut Binding,
        premises: &mut Vec<String>,
        out: &mut Vec<(Binding, Vec<String>)>,
    ) {
        if i == lits.len() {
            out.push((binding.clone(), premises.clone()));
            return;
        }
        match &lits[i] {
            Lit::Atom(pat) => {
                for (b, k) in self.atom(pat, binding) {
                    let mut b = b;
                    premises.push(k);
                    self.body(lits, i + 1, &mut b, premises, out);
                    premises.pop();
                }
            }
            Lit::Cmp(l, op, r) => {
                if *op == CmpOp::Eq
                    && let Expr::Term(Term::Var(v)) = l
                    && !binding.contains_key(v)
                {
                    if let Some(val) = self.value(r, binding) {
                        binding.insert(v.clone(), val);
                        self.body(lits, i + 1, binding, premises, out);
                        binding.remove(v);
                    }
                    return;
                }
                let holds = match compare(l, *op, r, binding) {
                    Ok(h) => h,
                    Err(e) => {
                        self.report(e);
                        false
                    }
                };
                if holds {
                    self.body(lits, i + 1, binding, premises, out);
                }
            }
            Lit::Agg {
                var,
                func,
                expr,
                over,
            } => {
                let Some((val, used)) = self.aggregate(*func, expr, over, binding) else {
                    return;
                };
                if let Some(bound) = binding.get(var) {
                    if !term_eq(bound, &val) {
                        return;
                    }
                    let n = premises.len();
                    premises.extend(used);
                    self.body(lits, i + 1, binding, premises, out);
                    premises.truncate(n);
                } else {
                    binding.insert(var.clone(), val);
                    let n = premises.len();
                    premises.extend(used);
                    self.body(lits, i + 1, binding, premises, out);
                    premises.truncate(n);
                    binding.remove(var);
                }
            }
        }
    }

    fn atom(&self, pat: &Atom, binding: &Binding) -> Vec<(Binding, String)> {
        let Some(keys) = self.index.get(&(pat.rel.clone(), pat.neg)) else {
            return vec![];
        };
        let mut out = Vec::new();
        for k in keys {
            let mut b = binding.clone();
            if unify(pat, &self.db[k].0, &mut b) {
                out.push((b, k.clone()));
            }
        }
        out
    }

    /// Distinct solutions of `over` under `binding`, folded in a canonical
    /// order (by solution) so that the result does not depend on statement
    /// order, even for floating-point sums.
    fn aggregate(
        &mut self,
        func: AggFn,
        expr: &Expr,
        over: &[Atom],
        binding: &Binding,
    ) -> Option<(Term, Vec<String>)> {
        let mut solutions: Vec<(Binding, Vec<String>)> = vec![(binding.clone(), vec![])];
        for pat in over {
            let mut next = Vec::new();
            for (b, used) in &solutions {
                for (b2, k) in self.atom(pat, b) {
                    let mut u = used.clone();
                    u.push(k);
                    next.push((b2, u));
                }
            }
            solutions = next;
        }
        let mut distinct: BTreeMap<String, (Binding, Vec<String>)> = BTreeMap::new();
        for (b, used) in solutions {
            let key: Vec<String> = b.iter().map(|(k, v)| format!("{k}={v}")).collect();
            distinct.entry(key.join(";")).or_insert((b, used));
        }
        let mut used_all: Vec<String> = distinct.values().flat_map(|(_, u)| u.clone()).collect();
        used_all.sort();
        used_all.dedup();
        if distinct.is_empty() {
            // Reasoning from absence must show in the grounds: say what was
            // looked for and not found. Marked with ∅, it is not an atom key.
            let mut looked: Vec<String> =
                over.iter().map(|a| subst(a, binding).to_string()).collect();
            looked.sort();
            used_all = vec![format!(
                "{ABSENT}none in this context: {}",
                looked.join(", ")
            )];
        }
        if func == AggFn::Count {
            return Some((Term::Num(distinct.len() as f64, Dim::NONE), used_all));
        }
        let mut acc: Option<(f64, Dim)> = None;
        for (b, _) in distinct.values() {
            let (x, dim) = match self.value(expr, b)? {
                Term::Num(x, d) => (x, d),
                other => {
                    self.report(EvalErr::NotNumber(other.to_string()));
                    return None;
                }
            };
            acc = Some(match acc {
                None => (x, dim),
                Some((_, ad)) if ad != dim => {
                    self.report(EvalErr::Dim(format!("aggregating [{ad}] with [{dim}]")));
                    return None;
                }
                Some((a, ad)) => match func {
                    AggFn::Sum => (a + x, ad),
                    AggFn::Min => (a.min(x), ad),
                    AggFn::Max => (a.max(x), ad),
                    AggFn::Count => unreachable!(),
                },
            });
        }
        match (func, acc) {
            (_, Some((v, d))) => Some((Term::Num(v, d), used_all)),
            (AggFn::Sum, None) => Some((Term::Num(0.0, Dim::NONE), used_all)),
            _ => None,
        }
    }

    fn value(&mut self, e: &Expr, b: &Binding) -> Option<Term> {
        match eval_expr(e, b) {
            Ok(v) => Some(v),
            Err(err) => {
                self.report(err);
                None
            }
        }
    }

    fn report(&mut self, e: EvalErr) {
        if let EvalErr::Dim(msg) | EvalErr::NotNumber(msg) = e {
            self.errors.insert(format!("rule `{}`: {msg}", self.rule));
        }
    }
}

/// Pattern roles must all be present in the ground atom; the atom may have more.
fn unify(pat: &Atom, ground: &Atom, b: &mut Binding) -> bool {
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
        (Term::Num(x, dx), Term::Num(y, dy)) => {
            dx == dy && (x - y).abs() <= 1e-12 * x.abs().max(y.abs()).max(1.0)
        }
        _ => a == b,
    }
}

pub fn subst(a: &Atom, b: &Binding) -> Atom {
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

enum EvalErr {
    /// An unbound variable: the literal simply does not match.
    Unbound,
    /// A symbol where a number was needed.
    NotNumber(String),
    /// Quantities of incompatible dimensions.
    Dim(String),
}

fn eval_expr(e: &Expr, b: &Binding) -> Result<Term, EvalErr> {
    match e {
        Expr::Term(Term::Var(v)) => b.get(v).cloned().ok_or(EvalErr::Unbound),
        Expr::Term(t) => Ok(t.clone()),
        Expr::Bin(l, op, r) => {
            let (lv, rv) = (eval_expr(l, b)?, eval_expr(r, b)?);
            let (Term::Num(x, dx), Term::Num(y, dy)) = (&lv, &rv) else {
                return Err(EvalErr::NotNumber(format!("{lv} {op} {rv}")));
            };
            let (x, y, dx, dy) = (*x, *y, *dx, *dy);
            let same = |what: &str| {
                if dx == dy {
                    Ok(dx)
                } else {
                    Err(EvalErr::Dim(format!("{what} [{dx}] and [{dy}]")))
                }
            };
            let (v, d) = match op {
                '+' => (x + y, same("adding")?),
                '-' => (x - y, same("subtracting")?),
                '*' => (x * y, dx.times(dy)),
                '/' if y != 0.0 => (x / y, dx.per(dy)),
                '/' => return Err(EvalErr::NotNumber("division by zero".into())),
                '^' if !dy.is_none() => {
                    return Err(EvalErr::Dim(format!("exponent with dimension [{dy}]")));
                }
                // Integer powers stay bit-identical across platforms; `powf` goes through libm.
                '^' if y.fract() == 0.0 && y.abs() <= 64.0 => {
                    let n = y as i32;
                    let d = dx
                        .pow(n)
                        .ok_or_else(|| EvalErr::Dim("dimension exponent overflow".into()))?;
                    (x.powi(n), d)
                }
                '^' if dx.is_none() => (x.powf(y), Dim::NONE),
                '^' => {
                    return Err(EvalErr::Dim(format!(
                        "non-integer power of a quantity with dimension [{dx}]"
                    )));
                }
                _ => return Err(EvalErr::NotNumber(format!("operator {op}"))),
            };
            Ok(Term::Num(v, d))
        }
    }
}

fn compare(l: &Expr, op: CmpOp, r: &Expr, b: &Binding) -> Result<bool, EvalErr> {
    let (x, y) = (eval_expr(l, b)?, eval_expr(r, b)?);
    match (&x, &y) {
        (Term::Num(a, da), Term::Num(c, dc)) => {
            // Zero is comparable with any dimension: `?net = 0` reads naturally.
            if da != dc && *a != 0.0 && *c != 0.0 {
                return Err(EvalErr::Dim(format!("comparing [{da}] with [{dc}]")));
            }
            Ok(match op {
                CmpOp::Lt => a < c,
                CmpOp::Le => a <= c,
                CmpOp::Gt => a > c,
                CmpOp::Ge => a >= c,
                CmpOp::Eq => (a - c).abs() <= 1e-12 * a.abs().max(c.abs()).max(1.0),
                CmpOp::Ne => (a - c).abs() > 1e-12 * a.abs().max(c.abs()).max(1.0),
            })
        }
        _ => match op {
            CmpOp::Eq => Ok(x == y),
            CmpOp::Ne => Ok(x != y),
            _ => Err(EvalErr::NotNumber(format!("ordering {x} and {y}"))),
        },
    }
}

/// Reports every group that breaks a `unique` declaration, with the sources of
/// the atoms involved.
fn check_uniques(prog: &Program, db: &Db, conflicts: &mut BTreeMap<String, Conflict>) {
    for u in &prog.uniques {
        let mut groups: BTreeMap<Vec<String>, BTreeMap<String, Vec<String>>> = BTreeMap::new();
        for (atom, derivs) in db.values() {
            if atom.rel != u.rel || atom.neg {
                continue;
            }
            let get = |role: &str| {
                atom.args
                    .iter()
                    .find(|(r, _)| r == role)
                    .map(|(_, t)| t.to_string())
            };
            let (Some(keys), Some(val)) = (
                u.by.iter().map(|k| get(k)).collect::<Option<Vec<_>>>(),
                get(&u.role),
            ) else {
                continue;
            };
            groups
                .entry(keys)
                .or_default()
                .entry(val)
                .or_default()
                .extend(sources(derivs));
        }
        for (keys, vals) in groups {
            if vals.len() < 2 {
                continue;
            }
            let names: Vec<&String> = vals.keys().collect();
            let desc = format!(
                "unique {}({}) by ({}) = ({}): {}",
                u.rel,
                u.role,
                u.by.join(", "),
                keys.join(", "),
                names
                    .iter()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .join(" vs ")
            );
            let ranks: Vec<usize> = vals
                .values()
                .map(|srcs| {
                    srcs.iter()
                        .map(|s| source_rank(prog, s, db))
                        .max()
                        .unwrap_or(0)
                })
                .collect();
            let max = ranks.iter().copied().max().unwrap_or(0);
            let blame: Vec<String> = vals
                .iter()
                .zip(&ranks)
                .filter(|(_, r)| **r < max)
                .flat_map(|((_, srcs), _)| srcs.iter().map(|s| labelled(prog, s)))
                .collect();
            let mut it = vals.into_values();
            let first = it.next().unwrap_or_default();
            let mut rest: Vec<String> = it.flatten().collect();
            rest.sort();
            rest.dedup();
            conflicts.insert(
                desc.clone(),
                Conflict {
                    positive: desc,
                    kind: ConflictKind::Uniqueness,
                    sources_pos: first,
                    sources_neg: rest,
                    blame,
                },
            );
        }
    }
}

/// Rank of a fact by id, or of a rule's best derivation in `db`.
fn source_rank(prog: &Program, source: &str, db: &Db) -> usize {
    if let Some(f) = prog.facts.iter().find(|f| f.id == source) {
        return prog.status_rank.get(&f.status).copied().unwrap_or(0);
    }
    db.values()
        .flat_map(|(_, ds)| ds.iter())
        .filter(|d| d.source == source)
        .map(|d| d.rank)
        .max()
        .unwrap_or(0)
}

fn labelled(prog: &Program, source: &str) -> String {
    match prog.facts.iter().find(|f| f.id == source) {
        Some(f) => format!("{} [{}]", f.id, f.status),
        None => source.to_string(),
    }
}

/// Facts the atom rests on, transitively, with their ranks.
fn support_facts(prog: &Program, db: &Db, key: &str) -> Vec<(usize, String)> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![key.to_string()];
    while let Some(k) = stack.pop() {
        if !seen.insert(k.clone()) {
            continue;
        }
        let Some((_, derivs)) = db.get(&k) else {
            continue;
        };
        for d in derivs {
            if d.is_fact {
                out.insert((d.rank, labelled(prog, &d.source)));
            }
            stack.extend(d.premises.iter().cloned());
        }
    }
    out.into_iter().collect()
}

/// Reports every derived atom that matches a visible `forbid`, blaming the
/// least trusted facts it rests on when statuses differ.
fn check_forbids(prog: &Program, ctx: &Plane, db: &Db, conflicts: &mut BTreeMap<String, Conflict>) {
    for f in prog
        .forbids
        .iter()
        .filter(|f| prog.axes.plane_within(ctx, &f.plane))
    {
        for (key, (atom, derivs)) in db {
            if atom.rel != f.atom.rel
                || atom.neg != f.atom.neg
                || !unify(&f.atom, atom, &mut Binding::new())
            {
                continue;
            }
            let facts = support_facts(prog, db, key);
            let min = facts.iter().map(|(r, _)| *r).min().unwrap_or(0);
            let max = facts.iter().map(|(r, _)| *r).max().unwrap_or(0);
            let blame = if min < max {
                facts
                    .into_iter()
                    .filter(|(r, _)| *r == min)
                    .map(|(_, l)| l)
                    .collect()
            } else {
                vec![]
            };
            let desc = format!("forbidden {key}");
            conflicts.insert(
                desc.clone(),
                Conflict {
                    positive: desc,
                    kind: ConflictKind::Violation,
                    sources_pos: sources(derivs),
                    sources_neg: vec![],
                    blame,
                },
            );
        }
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
    if key.starts_with(ABSENT) {
        s.push_str(&format!("{pad}{key}\n"));
        return;
    }
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

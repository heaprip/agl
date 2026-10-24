//! Evaluation of a program in a context plane.
//!
//! A fact or rule is visible in context `c` when `c` lies within its plane;
//! this gives inheritance down nested planes. Evaluation is a naive fixpoint,
//! stratum by stratum (an aggregate needs its relations complete), that may
//! derive both `p` and `¬p`. Conflicts are then settled layer by layer, as in
//! defeasible logic (`decide`): strict beats defeasible, then the more trusted
//! side, then a declared `defeats` by team defeat, then the more specific
//! plane. Losers are blocked and the fixpoint is recomputed without them.
//! Unresolved and strict-vs-strict conflicts block both sides and are
//! reported, as are violations of `unique` declarations. `tests/oracle.rs`
//! checks the result against a reference defeasible logic.

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
    /// Why an atom derived in the closure does not hold: the conflict it
    /// lost, or the premises it fell with.
    pub defeated: BTreeMap<String, String>,
    /// Evaluation errors, such as adding quantities of different dimensions.
    pub errors: BTreeSet<String>,
    pub truncated: bool,
}

pub fn evaluate(prog: &Program, ctx: &Plane) -> Outcome {
    evaluate_in(prog, &Visibility::new(prog), ctx)
}

/// Facts and rules by plane, built once per program: a context then checks
/// each distinct plane once instead of each statement.
pub struct Visibility {
    facts: BTreeMap<Plane, Vec<usize>>,
    rules: BTreeMap<Plane, Vec<usize>>,
}

impl Visibility {
    pub fn new(prog: &Program) -> Self {
        let mut facts: BTreeMap<Plane, Vec<usize>> = BTreeMap::new();
        for (i, f) in prog.facts.iter().enumerate() {
            facts.entry(f.plane.clone()).or_default().push(i);
        }
        let mut rules: BTreeMap<Plane, Vec<usize>> = BTreeMap::new();
        for (i, r) in prog.rules.iter().enumerate() {
            rules.entry(r.plane.clone()).or_default().push(i);
        }
        Visibility { facts, rules }
    }

    /// Indices of the statements visible in `ctx`, in program order.
    fn visible(prog: &Program, by_plane: &BTreeMap<Plane, Vec<usize>>, ctx: &Plane) -> Vec<usize> {
        let mut out: Vec<usize> = by_plane
            .iter()
            .filter(|(p, _)| prog.axes.plane_within(ctx, p))
            .flat_map(|(_, ix)| ix.iter().copied())
            .collect();
        out.sort_unstable();
        out
    }
}

/// `evaluate` with the naive fixpoint: every round matches every rule
/// against the whole database. Kept as the reference that the semi-naive
/// fixpoint is checked against (H65).
pub fn evaluate_reference(prog: &Program, ctx: &Plane) -> Outcome {
    evaluate_mode(prog, &Visibility::new(prog), ctx, true)
}

/// `evaluate` with the statements already grouped by plane.
pub fn evaluate_in(prog: &Program, vis: &Visibility, ctx: &Plane) -> Outcome {
    evaluate_mode(prog, vis, ctx, false)
}

fn evaluate_mode(prog: &Program, vis: &Visibility, ctx: &Plane, naive: bool) -> Outcome {
    let facts: Vec<&Fact> = Visibility::visible(prog, &vis.facts, ctx)
        .into_iter()
        .map(|i| &prog.facts[i])
        .collect();
    let rules: Vec<&Rule> = Visibility::visible(prog, &vis.rules, ctx)
        .into_iter()
        .map(|i| &prog.rules[i])
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
            naive,
        );
        if truncated && !out.truncated {
            // Silent truncation turned "not derived" into "unknown" (found by
            // the ablation of H57, step 4): say it where the report shows it.
            out.errors.insert(format!(
                "closure stopped at {MAX_ATOMS} atoms in context {}: what is not derived may be missing",
                if ctx.is_empty() { "{}".to_string() } else { format!("{ctx:?}") }
            ));
        }
        out.truncated |= truncated;
        let newly = decide(prog, &db, &mut out);
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

#[derive(Clone, Copy, PartialEq)]
enum Label {
    In,
    /// Every derivation has a premise out.
    Out,
    /// Cannot win its conflict.
    Lost,
}

/// Settles conflicts layer by layer, as the proof conditions +∂/−∂ of
/// defeasible logic do. A derivation is applicable when all its premises are
/// in, alive while none is out. An atom is in once its applicable derivations
/// beat every live derivation of its complement; it has lost once even all
/// its live derivations cannot beat the complement's applicable ones; it is
/// out once nothing of it is alive. Each criterion of `resolve` favours a
/// side more as it gains derivations and its opponent loses them, so these
/// bounds decide a side as soon as undecided atoms can no longer change it.
/// Both sides of a conflict may lose: that is an unresolved or hard conflict.
///
/// An atom that only a loop of undecided atoms supports is out (well-founded
/// failure). Conflicts still open after that rest on each other in a cycle
/// and are decided together on everything alive. Returns the losers to block.
fn decide(prog: &Program, db: &Db, out: &mut Outcome) -> Vec<String> {
    let founded = Founded::new(db);
    let mut label: BTreeMap<&str, Label> = BTreeMap::new();
    let mut stuck = false;
    loop {
        let mut changed = false;
        for (key, (atom, derivs)) in db {
            if label.contains_key(key.as_str()) {
                continue;
            }
            let (app, live) = split(derivs, &label);
            let ckey = atom.complement().key();
            let opponent = db
                .get_key_value(&ckey)
                .map(|(k, (_, ds))| (k.as_str(), split(ds, &label)));
            let decided = match opponent {
                _ if live.is_empty() => Some(Label::Out),
                None => (!app.is_empty()).then_some(Label::In),
                Some((_, (_, clive))) if clive.is_empty() => (!app.is_empty()).then_some(Label::In),
                Some((ckey, (capp, clive))) => {
                    let wins = |a: &[&Derivation], b: &[&Derivation]| {
                        !a.is_empty()
                            && matches!(resolve(prog, &founded, a, b, key, ckey), Winner::Pos)
                    };
                    if wins(&app, &clive) {
                        Some(Label::In)
                    } else if !capp.is_empty() && !wins(&live, &capp) {
                        Some(Label::Lost)
                    } else if stuck {
                        Some(if wins(&live, &clive) {
                            Label::In
                        } else {
                            Label::Lost
                        })
                    } else {
                        None
                    }
                }
            };
            if let Some(l) = decided {
                label.insert(key, l);
                changed = true;
            }
        }
        if !changed {
            // Well-founded failure: what only a loop of undecided atoms could
            // support, with no base outside the loop, is out.
            let mut possible: BTreeSet<&str> = BTreeSet::new();
            loop {
                let before = possible.len();
                for (key, (_, derivs)) in db {
                    let k = key.as_str();
                    if possible.contains(k)
                        || matches!(label.get(k), Some(Label::Out | Label::Lost))
                    {
                        continue;
                    }
                    if label.get(k) == Some(&Label::In)
                        || derivs
                            .iter()
                            .any(|d| real(&d.premises).all(|p| possible.contains(p.as_str())))
                    {
                        possible.insert(k);
                    }
                }
                if possible.len() == before {
                    break;
                }
            }
            for key in db.keys() {
                if !possible.contains(key.as_str()) && !label.contains_key(key.as_str()) {
                    label.insert(key, Label::Out);
                    changed = true;
                }
            }
        }
        if changed {
            stuck = false;
        } else if stuck {
            break;
        } else {
            stuck = true;
        }
    }
    // Report: a loser beside a winner is defeated; two losers are a conflict.
    let mut newly = Vec::new();
    for (key, (atom, derivs)) in db {
        if label.get(key.as_str()) == Some(&Label::Out) {
            // It fell with its premises: name the ones that fell.
            let mut fell: Vec<&str> = derivs
                .iter()
                .flat_map(|d| real(&d.premises))
                .filter(|p| matches!(label.get(p.as_str()), Some(Label::Out | Label::Lost)))
                .map(String::as_str)
                .collect();
            fell.sort();
            fell.dedup();
            out.defeated.insert(
                key.clone(),
                format!("rests on {}, which did not hold", fell.join(", ")),
            );
        }
        if label.get(key.as_str()) != Some(&Label::Lost) {
            continue;
        }
        newly.push(key.clone());
        let ckey = atom.complement().key();
        let cderivs = &db[&ckey].1;
        if label.get(ckey.as_str()) != Some(&Label::Lost) {
            out.defeated.insert(
                key.clone(),
                format!("defeated by {}", sources(cderivs).join(", ")),
            );
        } else if !atom.neg {
            let (app, _) = split(derivs, &label);
            let (capp, _) = split(cderivs, &label);
            let kind = match resolve(prog, &founded, &app, &capp, key, &ckey) {
                Winner::None(kind) => kind,
                _ => ConflictKind::Unresolved,
            };
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
        }
    }
    newly
}

/// A derivation's applicable form (every premise in) and live form (no
/// premise out).
fn split<'a>(
    derivs: &'a [Derivation],
    label: &BTreeMap<&str, Label>,
) -> (Vec<&'a Derivation>, Vec<&'a Derivation>) {
    let is = |p: &String, l: Label| label.get(p.as_str()) == Some(&l);
    let app = derivs
        .iter()
        .filter(|d| real(&d.premises).all(|p| is(p, Label::In)))
        .collect();
    let live = derivs
        .iter()
        .filter(|d| !real(&d.premises).any(|p| is(p, Label::Out) || is(p, Label::Lost)))
        .collect();
    (app, live)
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

/// `founded` for one database, each key computed once: `decide` asks for the
/// same keys on every pass while the database stays the same.
struct Founded<'a> {
    db: &'a Db,
    memo: std::cell::RefCell<BTreeMap<String, Vec<&'a Derivation>>>,
}

impl<'a> Founded<'a> {
    fn new(db: &'a Db) -> Self {
        Founded {
            db,
            memo: Default::default(),
        }
    }

    fn get(&self, key: &str) -> Vec<&'a Derivation> {
        if let Some(ds) = self.memo.borrow().get(key) {
            return ds.clone();
        }
        let ds = founded(self.db, key);
        self.memo.borrow_mut().insert(key.to_string(), ds.clone());
        ds
    }
}

/// Derivations of `key` that stand without `key` itself: a derivation that
/// rests on its own conclusion neither supports it nor needs to be beaten.
fn founded<'a>(db: &'a Db, key: &str) -> Vec<&'a Derivation> {
    // Every atom of the closure was derived from facts. If no chain of
    // premises leads from `key` back to `key`, none of its premises needs it,
    // so every derivation stands; the search below is needed only on a cycle.
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut stack: Vec<&str> = db[key]
        .1
        .iter()
        .flat_map(|d| real(&d.premises).map(String::as_str))
        .collect();
    let mut cyclic = false;
    while let Some(k) = stack.pop() {
        if k == key {
            cyclic = true;
            break;
        }
        if !seen.insert(k) {
            continue;
        }
        let Some((_, ds)) = db.get(k) else {
            cyclic = true; // not in the closure: let the full search judge
            break;
        };
        stack.extend(
            ds.iter()
                .flat_map(|d| real(&d.premises).map(String::as_str)),
        );
    }
    if !cyclic {
        return db[key].1.iter().collect();
    }
    let mut without: BTreeSet<&str> = BTreeSet::new();
    let stands = |d: &Derivation, without: &BTreeSet<&str>| {
        real(&d.premises).all(|p| without.contains(p.as_str()))
    };
    loop {
        let before = without.len();
        for (k, (_, ds)) in db {
            if k != key && !without.contains(k.as_str()) && ds.iter().any(|d| stands(d, &without)) {
                without.insert(k);
            }
        }
        if without.len() == before {
            break;
        }
    }
    db[key].1.iter().filter(|d| stands(d, &without)).collect()
}

/// Which side of a conflict wins: `pos`, derivations of `key`, or `neg`,
/// derivations of its complement `ckey`.
fn resolve(
    prog: &Program,
    founded: &Founded,
    pos: &[&Derivation],
    neg: &[&Derivation],
    key: &str,
    ckey: &str,
) -> Winner {
    let ps = pos.iter().any(|d| d.strict);
    let ns = neg.iter().any(|d| d.strict);
    // Between two sides of the same strength, the more trusted one wins: an
    // LLM proposal against a textbook is a rejected candidate, not a
    // contradiction. Only derivations of the deciding strength count, so a
    // defeasible derivation cannot lend its trust to a strict one.
    let rank_of = |ds: &[&Derivation], strict: bool| {
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
    // Team defeat, as in defeasible logic: a side wins by priority when every
    // derivation of the other side is beaten by one of its own.
    let (fp, fn_) = (founded.get(key), founded.get(ckey));
    let pos: Vec<&Derivation> = pos
        .iter()
        .copied()
        .filter(|d| fp.iter().any(|f| std::ptr::eq(*f, *d)))
        .collect();
    let neg: Vec<&Derivation> = neg
        .iter()
        .copied()
        .filter(|d| fn_.iter().any(|f| std::ptr::eq(*f, *d)))
        .collect();
    let beats = |a: &[&Derivation], b: &[&Derivation]| {
        b.iter().all(|y| {
            a.iter()
                .any(|x| prog.defeats.contains(&(x.source.clone(), y.source.clone())))
        })
    };
    match (beats(&pos, &neg), beats(&neg, &pos)) {
        (true, false) => return Winner::Pos,
        (false, true) => return Winner::Neg,
        _ => {}
    }
    let more_specific = |a: &[&Derivation], b: &[&Derivation]| {
        a.iter().any(|x| {
            b.iter()
                .all(|y| prog.axes.strictly_within(&x.plane, &y.plane))
        })
    };
    match (more_specific(&pos, &neg), more_specific(&neg, &pos)) {
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

#[allow(clippy::too_many_arguments)]
fn closure(
    prog: &Program,
    facts: &[&Fact],
    rules: &[&Rule],
    strata: &BTreeMap<String, usize>,
    blocked: &BTreeSet<String>,
    top: usize,
    errors: &mut BTreeSet<String>,
    naive: bool,
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
    // A nesting whose two rules are visible is derived from labels, unless
    // one of its atoms lost a conflict: then its rules run as written.
    let nests: Vec<&Nesting> = prog
        .nestings
        .iter()
        .filter(|n| {
            let (b, s) = (n.base_id(), n.step_id());
            rules.iter().any(|r| r.id == b)
                && rules.iter().any(|r| r.id == s)
                && !blocked
                    .iter()
                    .any(|k| k.starts_with(&format!("{}(", n.rel)))
        })
        .collect();
    // Lazy ones (step 2b): only rule bodies read N and the edges are facts.
    let lazy: BTreeMap<String, Lazy> = nests
        .iter()
        .filter(|n| n.lazy && lazy_allowed(prog, n) && !rules.iter().any(|r| r.head.rel == n.edge))
        .map(|n| (n.rel.clone(), Lazy::build(n, &db)))
        .collect();
    let nests: Vec<&Nesting> = nests
        .into_iter()
        .filter(|n| !lazy.contains_key(&n.rel))
        .collect();
    let by_labels = |r: &Rule| {
        nests
            .iter()
            .copied()
            .chain(lazy.values().map(|l| &l.nest))
            .any(|n| r.id == n.base_id() || r.id == n.step_id())
    };
    for level in levels {
        let at = |rel: &str| strata.get(rel).copied().unwrap_or(0) == level;
        let layer: Vec<&Rule> = rules
            .iter()
            .copied()
            .filter(|r| at(&r.head.rel) && !by_labels(r))
            .collect();
        let here: Vec<&Nesting> = nests.iter().copied().filter(|n| at(&n.rel)).collect();
        loop {
            if fixpoint(&mut db, &layer, blocked, errors, naive, &lazy) {
                settle(&mut db, top);
                return (db, true);
            }
            let mut added = false;
            for n in &here {
                added |= nest(&mut db, n);
            }
            if db.len() > MAX_ATOMS {
                settle(&mut db, top);
                return (db, true);
            }
            if !added {
                break;
            }
        }
    }
    settle(&mut db, top);
    (db, false)
}

/// Adds the atoms of a nesting N with the derivations its two rules would
/// give, read from labels in one pass (H61): `ID_base` for every edge atom,
/// `ID_step` for every edge atom E(x, z) and atom N(z, y). N atoms that came
/// from elsewhere (facts, other rules) count as a last step of a path. Called
/// again after other rules of the stratum add edges; returns whether anything
/// was added.
fn nest(db: &mut Db, n: &Nesting) -> bool {
    let pick = |a: &Atom, roles: &(String, String)| -> Option<(Term, Term)> {
        let get = |r: &str| a.args.iter().find(|(x, _)| x == r).map(|(_, t)| t.clone());
        Some((get(&roles.0)?, get(&roles.1)?))
    };
    let (base_id, step_id) = (n.base_id(), n.step_id());
    // (key, x, y) of edge atoms; (key, z, y) of N atoms from elsewhere.
    let mut edges: Vec<(String, Term, Term)> = Vec::new();
    let mut given: Vec<(String, Term, Term)> = Vec::new();
    for (k, (a, ds)) in db.iter() {
        if a.neg {
            continue;
        }
        if a.rel == n.edge {
            if let Some((x, y)) = pick(a, &n.edge_roles) {
                edges.push((k.clone(), x, y));
            }
        } else if a.rel == n.rel
            && ds
                .iter()
                .any(|d| d.source != base_id && d.source != step_id)
            && let Some((z, y)) = pick(a, &n.roles)
        {
            given.push((k.clone(), z, y));
        }
    }
    // Nodes by printed term; a given N(z, y) is an edge to a fresh copy of y
    // that has no edges out, so a path reaching it ends with that step.
    let mut terms: BTreeMap<String, Term> = BTreeMap::new();
    let mut graph: Vec<(String, String)> = Vec::new();
    for (_, x, y) in &edges {
        let (sx, sy) = (x.to_string(), y.to_string());
        terms.insert(sx.clone(), x.clone());
        terms.insert(sy.clone(), y.clone());
        graph.push((sx, sy));
    }
    for (_, z, y) in &given {
        let sz = z.to_string();
        terms.insert(sz.clone(), z.clone());
        terms.insert(format!("\0{y}"), y.clone());
        graph.push((sz, format!("\0{y}")));
    }
    let labels = crate::label::Labels::build(graph.iter().map(|(a, b)| (a.as_str(), b.as_str())));
    let mut out: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (_, x, y) in &edges {
        out.entry(x.to_string()).or_default().push(y.to_string());
    }
    // z -> keys of the N(z, y) atoms that will hold.
    let mut holds: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut derived: Vec<(Atom, String)> = Vec::new();
    for t in labels.names() {
        let y = &terms[t];
        let fresh = t.starts_with('\0');
        for d in labels.descendants(t) {
            // To a fresh copy, at least one edge must come first: the given
            // atom alone is not derived.
            let holds_here = if fresh {
                out.get(d)
                    .is_some_and(|qs| qs.iter().any(|q| labels.within(q, t)))
            } else {
                labels.reaches(d, t)
            };
            if d.starts_with('\0') || !holds_here {
                continue;
            }
            let atom = Atom::new(
                n.rel.clone(),
                vec![
                    (n.roles.0.clone(), terms[d].clone()),
                    (n.roles.1.clone(), y.clone()),
                ],
                false,
            );
            let key = atom.key();
            if holds.entry(d.to_string()).or_default().insert(key.clone()) {
                derived.push((atom, key));
            }
        }
    }
    for (k, z, _) in &given {
        holds.entry(z.to_string()).or_default().insert(k.clone());
    }
    let mut atoms: BTreeMap<String, Atom> = derived.into_iter().map(|(a, k)| (k, a)).collect();
    let mut new: Vec<(String, Derivation)> = Vec::new();
    let derivation = |source: &str, premises: Vec<String>| Derivation {
        source: source.to_string(),
        is_fact: false,
        strict: true,
        plane: Plane::new(),
        premises,
        rank: 0,
    };
    for (ek, x, y) in &edges {
        let base = Atom::new(
            n.rel.clone(),
            vec![
                (n.roles.0.clone(), x.clone()),
                (n.roles.1.clone(), y.clone()),
            ],
            false,
        );
        let bk = base.key();
        atoms.entry(bk.clone()).or_insert(base);
        new.push((bk, derivation(&base_id, vec![ek.clone()])));
        for nk in holds.get(&y.to_string()).into_iter().flatten() {
            // N(y, w) for this edge's genus y gives N(x, w).
            let w = db
                .get(nk)
                .map(|(a, _)| a)
                .or_else(|| atoms.get(nk))
                .and_then(|a| pick(a, &n.roles))
                .map(|(_, w)| w)
                .expect("an N atom of the closure");
            let head = Atom::new(
                n.rel.clone(),
                vec![(n.roles.0.clone(), x.clone()), (n.roles.1.clone(), w)],
                false,
            );
            let hk = head.key();
            atoms.entry(hk.clone()).or_insert(head);
            let mut premises = vec![ek.clone(), nk.clone()];
            premises.sort();
            premises.dedup();
            new.push((hk, derivation(&step_id, premises)));
        }
    }
    let mut added = false;
    for (key, d) in new {
        let atom = atoms.get(&key).cloned().expect("atom of a derivation");
        let entry = db.entry(key).or_insert_with(|| (atom, vec![]));
        if !entry
            .1
            .iter()
            .any(|x| x.source == d.source && x.premises == d.premises)
        {
            entry.1.push(d);
            added = true;
        }
    }
    added
}

fn real(premises: &[String]) -> impl Iterator<Item = &String> {
    premises.iter().filter(|p| !p.starts_with(ABSENT))
}

/// Strength and trust of every derivation, read through the whole closure.
/// Taken while saturating, they would freeze at the round a rule first fired,
/// before a premise gained its strict or more trusted derivation.
///
/// A derivation is strict when it is a fact, or its rule is strict and every
/// premise has a strict derivation: the strict closure. A strict derivation's
/// rank is its weakest premise's best strict rank, so a defeasible derivation
/// cannot lend trust to a strict one; a defeasible derivation's rank is its
/// weakest premise's rank. An atom's rank is that of its best derivation,
/// strength first, as in conflicts: a strict atom's rank is its best strict
/// derivation's. Both are least fixpoints, so a cycle cannot raise them.
fn settle(db: &mut Db, top: usize) {
    let mut strict: BTreeSet<String> = BTreeSet::new();
    loop {
        let before = strict.len();
        for (k, (_, ds)) in db.iter() {
            if !strict.contains(k)
                && ds.iter().any(|d| {
                    d.is_fact || (d.strict && real(&d.premises).all(|p| strict.contains(p)))
                })
            {
                strict.insert(k.clone());
            }
        }
        if strict.len() == before {
            break;
        }
    }
    for (_, ds) in db.values_mut() {
        for d in ds.iter_mut().filter(|d| !d.is_fact) {
            d.strict = d.strict && real(&d.premises).all(|p| strict.contains(p));
        }
    }
    loop {
        let best: BTreeMap<String, usize> = db
            .iter()
            .map(|(k, (_, ds))| {
                let s = strict.contains(k);
                let r = ds.iter().filter(|d| d.strict || !s).map(|d| d.rank).max();
                (k.clone(), r.unwrap_or(0))
            })
            .collect();
        let mut changed = false;
        for (_, ds) in db.values_mut() {
            for d in ds.iter_mut().filter(|d| !d.is_fact) {
                // A strict derivation's premises are all strict atoms.
                let rank = real(&d.premises)
                    .map(|p| best.get(p).copied().unwrap_or(0))
                    .min()
                    .unwrap_or(top);
                if rank > d.rank {
                    d.rank = rank;
                    changed = true;
                }
            }
        }
        if !changed {
            return;
        }
    }
}

/// May a nesting be lazy? Only if nothing but rule bodies reads N: no other
/// rule derives N or its complement, no fact denies it, no aggregate, query,
/// forbid, unique or compare reads it.
fn lazy_allowed(prog: &Program, n: &Nesting) -> bool {
    let own = |r: &Rule| r.id == n.base_id() || r.id == n.step_id();
    let rel = n.rel.as_str();
    !prog.rules.iter().any(|r| {
        (r.head.rel == rel && !own(r))
            || r.body.iter().any(|l| match l {
                Lit::Agg { over, .. } => over.iter().any(|a| a.rel == rel),
                _ => false,
            })
    }) && !prog.facts.iter().any(|f| f.atom.rel == rel && f.atom.neg)
        && !prog.queries.iter().any(|q| q.atom.rel == rel)
        && !prog.forbids.iter().any(|f| f.atom.rel == rel)
        && !prog.uniques.iter().any(|u| u.rel == rel)
        && !prog
            .compares
            .iter()
            .any(|c| c.left.0 == rel || c.right.0 == rel)
}

/// A lazy nesting (H61, step 2b): labels over the edges, and the atoms of N
/// made only for the pairs rule bodies match, each with its cone — every
/// atom N(z, y) on a path from x to y — so that every atom made has the
/// derivations of step 2a.
pub(crate) struct Lazy {
    nest: Nesting,
    labels: crate::label::Labels,
    terms: BTreeMap<String, Term>,
    /// x -> (genus, key of the edge atom)
    out: BTreeMap<String, Vec<(String, String)>>,
    /// z -> (y, key) of N atoms from elsewhere
    given: BTreeMap<String, Vec<(String, String)>>,
}

impl Lazy {
    fn build(n: &Nesting, db: &Db) -> Self {
        let pick = |a: &Atom, roles: &(String, String)| -> Option<(Term, Term)> {
            let get = |r: &str| a.args.iter().find(|(x, _)| x == r).map(|(_, t)| t.clone());
            Some((get(&roles.0)?, get(&roles.1)?))
        };
        let mut terms: BTreeMap<String, Term> = BTreeMap::new();
        let mut out: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
        let mut given: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
        let mut graph: Vec<(String, String)> = Vec::new();
        for (k, (a, _)) in db {
            if a.neg {
                continue;
            }
            if a.rel == n.edge
                && let Some((x, y)) = pick(a, &n.edge_roles)
            {
                let (sx, sy) = (x.to_string(), y.to_string());
                terms.insert(sx.clone(), x);
                terms.insert(sy.clone(), y);
                out.entry(sx.clone())
                    .or_default()
                    .push((sy.clone(), k.clone()));
                graph.push((sx, sy));
            } else if a.rel == n.rel
                && let Some((z, y)) = pick(a, &n.roles)
            {
                let (sz, sy) = (z.to_string(), y.to_string());
                terms.insert(sz.clone(), z);
                terms.insert(sy.clone(), y);
                given
                    .entry(sz.clone())
                    .or_default()
                    .push((sy.clone(), k.clone()));
                graph.push((sz, format!("\0{sy}")));
            }
        }
        let labels =
            crate::label::Labels::build(graph.iter().map(|(a, b)| (a.as_str(), b.as_str())));
        Lazy {
            nest: n.clone(),
            labels,
            terms,
            out,
            given,
        }
    }

    /// Does N(x, y) follow from the edges: a path of edges to y, or of edges
    /// and then a given N atom?
    fn holds(&self, x: &str, y: &str) -> bool {
        self.labels.reaches(x, y)
            || self.out.get(x).is_some_and(|qs| {
                let fresh = format!("\0{y}");
                qs.iter().any(|(q, _)| self.labels.within(q, &fresh))
            })
    }

    /// Pairs (x, y) where N holds, with x or y fixed when given.
    fn pairs(&self, x: Option<&str>, y: Option<&str>, diagonal: bool) -> Vec<(String, String)> {
        let real = |s: &str| !s.starts_with('\0');
        let genus = |s: &str| s.strip_prefix('\0').unwrap_or(s).to_string();
        let below = |y: &str| -> BTreeSet<String> {
            let fresh = format!("\0{y}");
            self.labels
                .descendants(y)
                .into_iter()
                .chain(self.labels.descendants(&fresh))
                .filter(|d| real(d))
                .map(str::to_string)
                .collect()
        };
        let mut out: BTreeSet<(String, String)> = BTreeSet::new();
        match (x, y) {
            (Some(x), Some(y)) => {
                if self.holds(x, y) {
                    out.insert((x.to_string(), y.to_string()));
                }
            }
            (None, Some(y)) => {
                for d in below(y) {
                    if self.holds(&d, y) {
                        out.insert((d, y.to_string()));
                    }
                }
            }
            (Some(x), None) => {
                let ys: BTreeSet<String> =
                    self.labels.ancestors(x).into_iter().map(genus).collect();
                for y in ys {
                    if self.holds(x, &y) {
                        out.insert((x.to_string(), y));
                    }
                }
            }
            (None, None) if diagonal => {
                for t in self.labels.names().filter(|t| real(t)) {
                    if self.holds(t, t) {
                        out.insert((t.to_string(), t.to_string()));
                    }
                }
            }
            (None, None) => {
                let ys: BTreeSet<String> = self.labels.names().map(genus).collect();
                for y in ys {
                    for d in below(&y) {
                        if self.holds(&d, &y) {
                            out.insert((d, y.clone()));
                        }
                    }
                }
            }
        }
        out.into_iter().collect()
    }

    /// The two-role atom N(x, y).
    fn atom(&self, x: &str, y: &str) -> Atom {
        Atom::new(
            self.nest.rel.clone(),
            vec![
                (self.nest.roles.0.clone(), self.terms[x].clone()),
                (self.nest.roles.1.clone(), self.terms[y].clone()),
            ],
            false,
        )
    }

    /// Makes N(x, y) and every N(z, y) on a path from x to y, each with the
    /// derivations of its two rules.
    fn cone(&self, x: &str, y: &str, db: &mut Db) {
        let fresh = format!("\0{y}");
        let mut cone: BTreeSet<&str> = self
            .labels
            .descendants(y)
            .into_iter()
            .chain(self.labels.descendants(&fresh))
            .filter(|z| !z.starts_with('\0') && self.labels.within(x, z))
            .collect();
        cone.retain(|z| self.holds(z, y));
        let derivation = |source: String, premises: Vec<String>| Derivation {
            source,
            is_fact: false,
            strict: true,
            plane: Plane::new(),
            premises,
            rank: 0,
        };
        for z in cone {
            let head = self.atom(z, y);
            let key = head.key();
            let mut ds: Vec<Derivation> = Vec::new();
            for (q, ek) in self.out.get(z).into_iter().flatten() {
                if q == y {
                    ds.push(derivation(self.nest.base_id(), vec![ek.clone()]));
                }
                let mut via: Vec<String> = Vec::new();
                if self.holds(q, y) {
                    via.push(self.atom(q, y).key());
                }
                via.extend(
                    self.given
                        .get(q.as_str())
                        .into_iter()
                        .flatten()
                        .filter(|(w, _)| w == y)
                        .map(|(_, k)| k.clone()),
                );
                for nk in via {
                    let mut premises = vec![ek.clone(), nk];
                    premises.sort();
                    premises.dedup();
                    ds.push(derivation(self.nest.step_id(), premises));
                }
            }
            let entry = db.entry(key).or_insert_with(|| (head, vec![]));
            for d in ds {
                if !entry
                    .1
                    .iter()
                    .any(|x| x.source == d.source && x.premises == d.premises)
                {
                    entry.1.push(d);
                }
            }
        }
    }
}

/// Saturates `db` with one stratum of rules; returns true if truncated.
///
/// Semi-naive (H65): after the first round, a match must take at least one
/// atom literal from the atoms new in the last round; the others come from
/// the whole database. A match of old atoms only was found in an earlier
/// round. Aggregates read lower strata, which do not change here. `naive`
/// matches everything every round: the reference.
fn fixpoint(
    db: &mut Db,
    rules: &[&Rule],
    blocked: &BTreeSet<String>,
    errors: &mut BTreeSet<String>,
    naive: bool,
    lazy: &BTreeMap<String, Lazy>,
) -> bool {
    // Atoms new in the last round; None in the first round: all are new.
    let mut fresh: Option<BTreeSet<String>> = None;
    loop {
        let mut added = false;
        let index = Index::new(db.iter());
        let delta = fresh
            .as_ref()
            .filter(|_| !naive)
            .map(|f| Index::new(db.iter().filter(|(k, _)| f.contains(*k))));
        let mut new: Vec<(Atom, Derivation)> = Vec::new();
        let wanted: std::cell::RefCell<BTreeSet<(String, String, String)>> = Default::default();
        for r in rules {
            let mut matches = Vec::new();
            let body = schedule(r);
            let mut ctx = Matcher {
                index: &index,
                forced: None,
                lazy,
                wanted: &wanted,
                rule: &r.id,
                errors: &mut *errors,
            };
            match &delta {
                None => ctx.body(&body, 0, &mut Binding::new(), &mut Vec::new(), &mut matches),
                Some(d) => {
                    for (i, _) in body
                        .iter()
                        .enumerate()
                        .filter(|(_, l)| matches!(l, Lit::Atom(_)))
                    {
                        ctx.forced = Some((i, d));
                        ctx.body(&body, 0, &mut Binding::new(), &mut Vec::new(), &mut matches);
                    }
                }
            }
            for (binding, mut premises) in matches {
                // A body is a conjunction: its premises form a set, not a sequence.
                premises.sort();
                premises.dedup();
                let head = subst(&r.head, &binding);
                if !head.is_ground() {
                    continue;
                }
                // The rule's own strength for now; `settle` reads it through the premises.
                new.push((
                    head,
                    Derivation {
                        source: r.id.clone(),
                        is_fact: false,
                        strict: r.strength == Strength::Strict,
                        plane: r.plane.clone(),
                        premises,
                        rank: 0,
                    },
                ));
            }
        }
        let mut born: BTreeSet<String> = BTreeSet::new();
        for (head, d) in new {
            let key = head.key();
            if blocked.contains(&key) {
                continue;
            }
            if !db.contains_key(&key) {
                born.insert(key.clone());
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
        // Atoms of lazy nestings that matches rest on, with their cones. They
        // held already, so they give no new match.
        for (rel, x, y) in wanted.into_inner() {
            lazy[&rel].cone(&x, &y, db);
        }
        if db.len() > MAX_ATOMS {
            return true;
        }
        // A new derivation of an old atom gives no new match.
        if !added || (!naive && born.is_empty()) {
            return false;
        }
        fresh = Some(born);
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

/// Atoms of the database by relation, and by relation and the symbol in one
/// role, so a pattern with a known symbol does not scan the whole relation.
/// Numbers are not indexed: they compare with a tolerance.
struct Index<'a> {
    by_rel: BTreeMap<String, Vec<(&'a String, &'a Atom)>>,
    by_sym: BTreeMap<String, Vec<(&'a String, &'a Atom)>>,
}

fn rel_key(rel: &str, neg: bool) -> String {
    format!("{rel}\u{1}{neg}")
}

fn sym_key(rel: &str, neg: bool, role: &str, sym: &str) -> String {
    format!("{rel}\u{1}{neg}\u{1}{role}\u{1}{sym}")
}

impl<'a> Index<'a> {
    fn new(atoms: impl Iterator<Item = (&'a String, &'a (Atom, Vec<Derivation>))>) -> Self {
        let mut by_rel: BTreeMap<String, Vec<_>> = BTreeMap::new();
        let mut by_sym: BTreeMap<String, Vec<_>> = BTreeMap::new();
        for (k, (a, _)) in atoms {
            by_rel
                .entry(rel_key(&a.rel, a.neg))
                .or_default()
                .push((k, a));
            for (role, t) in &a.args {
                if let Term::Sym(v) = t {
                    by_sym
                        .entry(sym_key(&a.rel, a.neg, role, v))
                        .or_default()
                        .push((k, a));
                }
            }
        }
        Index { by_rel, by_sym }
    }

    /// Atoms that can match `pat` under `binding`: the shortest list among
    /// the roles with a known symbol, else the whole relation. Lists keep
    /// database order, so matching order does not change.
    fn candidates(&self, pat: &Atom, binding: &Binding) -> &[(&'a String, &'a Atom)] {
        let mut best: Option<&Vec<_>> = None;
        for (role, t) in &pat.args {
            let sym = match t {
                Term::Sym(v) => v,
                Term::Var(v) => match binding.get(v) {
                    Some(Term::Sym(s)) => s,
                    _ => continue,
                },
                Term::Num(..) => continue,
            };
            let Some(list) = self.by_sym.get(&sym_key(&pat.rel, pat.neg, role, sym)) else {
                return &[];
            };
            if best.is_none_or(|b| list.len() < b.len()) {
                best = Some(list);
            }
        }
        match best {
            Some(list) => list,
            None => self
                .by_rel
                .get(&rel_key(&pat.rel, pat.neg))
                .map_or(&[], Vec::as_slice),
        }
    }
}

struct Matcher<'a> {
    index: &'a Index<'a>,
    /// The atom literal at this position matches only atoms of this index
    /// (the last round's new atoms).
    forced: Option<(usize, &'a Index<'a>)>,
    /// Lazy nestings by relation; matched from labels, not from the index.
    lazy: &'a BTreeMap<String, Lazy>,
    /// (relation, x, y) of lazy atoms matched in this round.
    wanted: &'a std::cell::RefCell<BTreeSet<(String, String, String)>>,
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
                let lazy = (!pat.neg).then(|| self.lazy.get(&pat.rel)).flatten();
                let found = match (self.forced, lazy) {
                    // A lazy relation does not change within the stratum.
                    (Some((at, _)), Some(_)) if at == i => return,
                    (_, Some(l)) => self.lazy_atom(l, pat, binding),
                    (Some((at, d)), None) if at == i => self.atom(d, pat, binding),
                    _ => self.atom(self.index, pat, binding),
                };
                for (b, k) in found {
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

    /// Matches of `pat` on a lazy nesting: the pairs the labels give, each
    /// as the two-role atom the rules would derive, and atoms of N already in
    /// the database (facts, atoms made earlier).
    fn lazy_atom(&self, l: &Lazy, pat: &Atom, binding: &Binding) -> Vec<(Binding, String)> {
        let side = |role: &str| -> (Option<String>, Option<&str>) {
            match pat.args.iter().find(|(r, _)| r == role).map(|(_, t)| t) {
                Some(Term::Var(v)) => match binding.get(v) {
                    Some(t) => (Some(t.to_string()), None),
                    None => (None, Some(v.as_str())),
                },
                Some(t) => (Some(t.to_string()), None),
                None => (None, None),
            }
        };
        let ((x, vx), (y, vy)) = (side(&l.nest.roles.0), side(&l.nest.roles.1));
        let diagonal = vx.is_some() && vx == vy;
        let mut out = Vec::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for (a, b) in l.pairs(x.as_deref(), y.as_deref(), diagonal) {
            let ground = l.atom(&a, &b);
            let mut bind = binding.clone();
            if unify(pat, &ground, &mut bind) {
                let key = ground.key();
                seen.insert(key.clone());
                self.wanted.borrow_mut().insert((l.nest.rel.clone(), a, b));
                out.push((bind, key));
            }
        }
        out.extend(
            self.atom(self.index, pat, binding)
                .into_iter()
                .filter(|(_, k)| !seen.contains(k)),
        );
        out
    }

    fn atom(&self, index: &Index, pat: &Atom, binding: &Binding) -> Vec<(Binding, String)> {
        let mut out = Vec::new();
        for (k, ground) in index.candidates(pat, binding) {
            if !fits(pat, ground, binding) {
                continue;
            }
            let mut b = binding.clone();
            if unify(pat, ground, &mut b) {
                out.push((b, (*k).clone()));
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
                for (b2, k) in self.atom(self.index, pat, b) {
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

/// A cheap test before `unify`, without copying the binding: roles present,
/// constants and bound variables equal. Unbound variables are left to `unify`.
fn fits(pat: &Atom, ground: &Atom, b: &Binding) -> bool {
    pat.args.iter().all(|(role, pt)| {
        let Some((_, gt)) = ground.args.iter().find(|(r, _)| r == role) else {
            return false;
        };
        match pt {
            Term::Var(v) => b.get(v).is_none_or(|bound| term_eq(bound, gt)),
            t => term_eq(t, gt),
        }
    })
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
            let (x, y) = (*x, *y);
            let overflow = || EvalErr::Dim("dimension exponent overflow".into());
            let same = |what: &str| {
                if dx == dy {
                    Ok(dx.clone())
                } else {
                    Err(EvalErr::Dim(format!("{what} [{dx}] and [{dy}]")))
                }
            };
            let (v, d) = match op {
                '+' => (x + y, same("adding")?),
                '-' => (x - y, same("subtracting")?),
                '*' => (x * y, dx.times(dy).ok_or_else(overflow)?),
                '/' if y != 0.0 => (x / y, dx.per(dy).ok_or_else(overflow)?),
                '/' => return Err(EvalErr::NotNumber("division by zero".into())),
                '^' if !dy.is_none() => {
                    return Err(EvalErr::Dim(format!("exponent with dimension [{dy}]")));
                }
                // Integer powers stay bit-identical across platforms; `powf` goes through libm.
                '^' if y.fract() == 0.0 && y.abs() <= 64.0 => {
                    let n = y as i32;
                    let d = dx.pow(n).ok_or_else(overflow)?;
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

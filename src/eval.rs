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

use crate::meta::{ClaimId, Entity, Evidence, Intension, Projection};
use crate::model::*;
use crate::units::Dim;

/// Prefix of a premise that records an aggregate which found nothing.
pub const ABSENT: &str = "∅ ";

/// Upper bound on derived atoms, against runaway arithmetic recursion; the
/// facts of a context do not count (a whole ontology is many facts).
const MAX_ATOMS: usize = 100_000;

#[derive(Clone, Debug)]
pub struct Derivation {
    pub entity: Entity,
    pub evidence: Evidence,
    pub is_fact: bool,
    /// Atoms of the database by number, ordered by their keys; `Db::key`
    /// gives the text.
    pub premises: Box<[Id]>,
    /// Trust: a fact's status rank; for a rule, its weakest premise.
    pub rank: usize,
}

impl Derivation {
    pub fn source(&self) -> &str {
        &self.evidence.operation
    }

    pub fn strict(&self) -> bool {
        self.evidence.strength == Strength::Strict
    }

    pub fn plane(&self) -> &Plane {
        &self.evidence.context
    }
}

/// The number of an atom in a closure: its place in the database (H61,
/// step 3b). Numbers follow insertion; everything that shapes the output
/// walks the database in key order.
pub type Id = u32;

/// Premise numbers from here on name an aggregate that found nothing.
const ABSENT_ID: Id = 1 << 31;

/// The closure: atoms with their derivations, by number. The key, the
/// printed atom, is stored once and indexes the atoms in text order, so two
/// atoms are the same when they print the same, as before numbers.
#[derive(Default, Debug)]
pub struct Db {
    context: Plane,
    entries: Vec<(Atom, Vec<Derivation>)>,
    keys: Vec<Name>,
    index: BTreeMap<Name, Id>,
    /// Premises of aggregates that found nothing, by number past `ABSENT_ID`.
    absent: Vec<Name>,
    absent_index: BTreeMap<Name, Id>,
}

impl Db {
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn id(&self, key: &str) -> Option<Id> {
        self.index.get(key).copied()
    }

    pub fn get(&self, key: &str) -> Option<&(Atom, Vec<Derivation>)> {
        self.id(key).map(|i| &self.entries[i as usize])
    }

    pub fn contains_key(&self, key: &str) -> bool {
        self.index.contains_key(key)
    }

    /// The text of an atom or of a premise that records an absence.
    pub fn key(&self, id: Id) -> &str {
        if id >= ABSENT_ID {
            &self.absent[(id - ABSENT_ID) as usize]
        } else {
            &self.keys[id as usize]
        }
    }

    pub fn at(&self, id: Id) -> &(Atom, Vec<Derivation>) {
        &self.entries[id as usize]
    }

    /// The premises of a derivation, as text, in their order.
    pub fn premise_keys<'s>(&'s self, d: &Derivation) -> impl Iterator<Item = &'s str> {
        d.premises.iter().map(|&p| self.key(p))
    }

    /// Numbers of the atoms in key order.
    pub fn ids(&self) -> impl Iterator<Item = Id> + '_ {
        self.index.values().copied()
    }

    /// Atoms in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&Name, &(Atom, Vec<Derivation>))> {
        self.index
            .iter()
            .map(|(k, &i)| (k, &self.entries[i as usize]))
    }

    pub fn keys(&self) -> impl Iterator<Item = &Name> {
        self.index.keys()
    }

    pub fn values(&self) -> impl Iterator<Item = &(Atom, Vec<Derivation>)> {
        self.index.values().map(|&i| &self.entries[i as usize])
    }

    /// Stable proposition node shared by all alternative derivations.
    pub fn claim_id(&self, id: Id) -> ClaimId {
        ClaimId::named("atom", self.key(id))
    }

    /// Every relation occurrence projected into this evaluated context.
    pub fn projections(&self) -> Vec<Projection<Atom>> {
        let mut out = Vec::new();
        for id in self.ids() {
            let (atom, derivations) = self.at(id);
            let claim = self.claim_id(id);
            for derivation in derivations {
                out.push(Projection {
                    claim: claim.clone(),
                    entity: derivation.entity.id.clone(),
                    context: self.context.clone(),
                    extent: atom.clone(),
                    evidence: derivation.evidence.id.clone(),
                });
            }
        }
        out
    }

    /// The number of the atom with this key, adding it if new.
    fn insert(&mut self, key: &str, atom: impl FnOnce() -> Atom) -> (Id, bool) {
        if let Some(i) = self.id(key) {
            return (i, false);
        }
        let i = self.entries.len() as Id;
        assert!(i < ABSENT_ID, "too many atoms to number");
        let key = Name::from(key);
        self.entries.push((atom(), Vec::with_capacity(1)));
        self.keys.push(key.clone());
        self.index.insert(key, i);
        (i, true)
    }

    /// The number of a premise given as text: an atom of the database, or
    /// an absence.
    fn premise(&mut self, key: &str) -> Id {
        if !key.starts_with(ABSENT) {
            return self.id(key).expect("a premise is an atom of the closure");
        }
        if let Some(&i) = self.absent_index.get(key) {
            return i;
        }
        let i = ABSENT_ID + self.absent.len() as Id;
        let key = Name::from(key);
        self.absent.push(key.clone());
        self.absent_index.insert(key, i);
        i
    }

    /// Premises as a set, ordered by key, as when they were text.
    fn premises(&self, mut ps: Vec<Id>) -> Box<[Id]> {
        ps.sort_by(|&a, &b| self.key(a).cmp(self.key(b)));
        ps.dedup();
        ps.into_boxed_slice()
    }

    /// Adds a derivation unless the atom has it already; returns whether it
    /// was added.
    fn derive(&mut self, id: Id, d: Derivation) -> bool {
        let ds = &mut self.entries[id as usize].1;
        if ds.iter().any(|x| x.evidence.id == d.evidence.id) {
            return false;
        }
        ds.push(d);
        true
    }
}

fn make_derivation(
    db: &Db,
    conclusion: &Atom,
    source: &Name,
    is_fact: bool,
    strength: Strength,
    plane: Plane,
    premises: Box<[Id]>,
    rank: usize,
) -> Derivation {
    let premise_claims: Vec<ClaimId> = premises.iter().map(|&id| db.claim_id(id)).collect();
    let conclusion_claim = ClaimId::named("atom", &conclusion.key());
    let evidence = Evidence::new(
        conclusion_claim,
        source.to_string(),
        premise_claims.clone(),
        strength,
        plane,
    );
    let intension = if is_fact {
        Intension::Primitive {
            source: source.to_string(),
        }
    } else {
        Intension::Derive {
            operation: source.to_string(),
            premises: premise_claims,
        }
    };
    let entity = Entity::new(intension, vec![evidence.id.clone()]);
    Derivation {
        entity,
        evidence,
        is_fact,
        premises,
        rank,
    }
}

impl std::ops::Index<&str> for Db {
    type Output = (Atom, Vec<Derivation>);
    fn index(&self, key: &str) -> &Self::Output {
        self.get(key).expect("an atom of the closure")
    }
}

impl<'a> IntoIterator for &'a Db {
    type Item = (&'a Name, &'a (Atom, Vec<Derivation>));
    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;
    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
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
    pub db: Db,
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
            ctx,
            top,
            &mut out.errors,
            naive,
        );
        if truncated && !out.truncated {
            // Silent truncation turned "not derived" into "unknown" (found by
            // the ablation of H57, step 4): say it where the report shows it.
            out.errors.insert(format!(
                "closure stopped at {MAX_ATOMS} derived atoms in context {}: what is not derived may be missing",
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
    // The complement of each atom, read from its key: `¬` leads a negation.
    let comp: Vec<Option<Id>> = (0..db.len() as Id)
        .map(|i| {
            let k = db.key(i);
            match k.strip_prefix('¬') {
                Some(pos) => db.id(pos),
                None => db.id(&format!("¬{k}")),
            }
        })
        .collect();
    let mut label: Vec<Option<Label>> = vec![None; db.len()];
    let mut stuck = false;
    loop {
        let mut changed = false;
        for i in db.ids() {
            if label[i as usize].is_some() {
                continue;
            }
            let derivs = &db.at(i).1;
            let (app, live) = split(derivs, &label);
            let opponent = comp[i as usize].map(|c| (c, split(&db.at(c).1, &label)));
            let decided = match opponent {
                _ if live.is_empty() => Some(Label::Out),
                None => (!app.is_empty()).then_some(Label::In),
                Some((_, (_, clive))) if clive.is_empty() => (!app.is_empty()).then_some(Label::In),
                Some((c, (capp, clive))) => {
                    let wins = |a: &[&Derivation], b: &[&Derivation]| {
                        !a.is_empty() && matches!(resolve(prog, &founded, a, b, i, c), Winner::Pos)
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
                label[i as usize] = Some(l);
                changed = true;
            }
        }
        if !changed {
            // Well-founded failure: what only a loop of undecided atoms could
            // support, with no base outside the loop, is out.
            let mut possible = vec![false; db.len()];
            loop {
                let mut grew = false;
                for i in db.ids() {
                    let k = i as usize;
                    if possible[k] || matches!(label[k], Some(Label::Out | Label::Lost)) {
                        continue;
                    }
                    if label[k] == Some(Label::In)
                        || db
                            .at(i)
                            .1
                            .iter()
                            .any(|d| real(&d.premises).all(|p| possible[p as usize]))
                    {
                        possible[k] = true;
                        grew = true;
                    }
                }
                if !grew {
                    break;
                }
            }
            for i in db.ids() {
                let k = i as usize;
                if !possible[k] && label[k].is_none() {
                    label[k] = Some(Label::Out);
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
    for (key, &i) in &db.index {
        let (atom, derivs) = db.at(i);
        if label[i as usize] == Some(Label::Out) {
            // It fell with its premises: name the ones that fell.
            let mut fell: Vec<&str> = derivs
                .iter()
                .flat_map(|d| real(&d.premises))
                .filter(|&p| matches!(label[p as usize], Some(Label::Out | Label::Lost)))
                .map(|p| db.key(p))
                .collect();
            fell.sort();
            fell.dedup();
            out.defeated.insert(
                key.to_string(),
                format!("rests on {}, which did not hold", fell.join(", ")),
            );
        }
        if label[i as usize] != Some(Label::Lost) {
            continue;
        }
        newly.push(key.to_string());
        let c = comp[i as usize].expect("a lost atom has a complement");
        let cderivs = &db.at(c).1;
        if label[c as usize] != Some(Label::Lost) {
            out.defeated.insert(
                key.to_string(),
                format!("defeated by {}", sources(cderivs).join(", ")),
            );
        } else if !atom.neg {
            let (app, _) = split(derivs, &label);
            let (capp, _) = split(cderivs, &label);
            let kind = match resolve(prog, &founded, &app, &capp, i, c) {
                Winner::None(kind) => kind,
                _ => ConflictKind::Unresolved,
            };
            out.conflicts.insert(
                key.to_string(),
                Conflict {
                    positive: key.to_string(),
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
    label: &[Option<Label>],
) -> (Vec<&'a Derivation>, Vec<&'a Derivation>) {
    let is = |p: Id, l: Label| label[p as usize] == Some(l);
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
    let mut s: Vec<String> = derivs.iter().map(|d| d.source().to_string()).collect();
    s.sort();
    s.dedup();
    s
}

enum Winner {
    Pos,
    Neg,
    None(ConflictKind),
}

/// `founded` for one database, each atom computed once: `decide` asks for
/// the same atoms on every pass while the database stays the same.
struct Founded<'a> {
    db: &'a Db,
    memo: std::cell::RefCell<BTreeMap<Id, Vec<&'a Derivation>>>,
}

impl<'a> Founded<'a> {
    fn new(db: &'a Db) -> Self {
        Founded {
            db,
            memo: Default::default(),
        }
    }

    fn get(&self, id: Id) -> Vec<&'a Derivation> {
        if let Some(ds) = self.memo.borrow().get(&id) {
            return ds.clone();
        }
        let ds = founded(self.db, id);
        self.memo.borrow_mut().insert(id, ds.clone());
        ds
    }
}

/// Derivations of atom `id` that stand without it: a derivation that rests
/// on its own conclusion neither supports it nor needs to be beaten.
fn founded(db: &Db, id: Id) -> Vec<&Derivation> {
    // Every atom of the closure was derived from facts. If no chain of
    // premises leads from `id` back to `id`, none of its premises needs it,
    // so every derivation stands; the search below is needed only on a cycle.
    let derivs = &db.at(id).1;
    let mut seen: BTreeSet<Id> = BTreeSet::new();
    let mut stack: Vec<Id> = derivs.iter().flat_map(|d| real(&d.premises)).collect();
    let mut cyclic = false;
    while let Some(k) = stack.pop() {
        if k == id {
            cyclic = true;
            break;
        }
        if !seen.insert(k) {
            continue;
        }
        stack.extend(db.at(k).1.iter().flat_map(|d| real(&d.premises)));
    }
    if !cyclic {
        return derivs.iter().collect();
    }
    let mut without = vec![false; db.len()];
    let stands = |d: &Derivation, without: &[bool]| real(&d.premises).all(|p| without[p as usize]);
    loop {
        let mut grew = false;
        for k in 0..db.len() as Id {
            if k != id && !without[k as usize] && db.at(k).1.iter().any(|d| stands(d, &without)) {
                without[k as usize] = true;
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    derivs.iter().filter(|d| stands(d, &without)).collect()
}

/// Which side of a conflict wins: `pos`, derivations of `key`, or `neg`,
/// derivations of its complement `ckey`.
fn resolve(
    prog: &Program,
    founded: &Founded,
    pos: &[&Derivation],
    neg: &[&Derivation],
    key: Id,
    ckey: Id,
) -> Winner {
    let ps = pos.iter().any(|d| d.strict());
    let ns = neg.iter().any(|d| d.strict());
    // Between two sides of the same strength, the more trusted one wins: an
    // LLM proposal against a textbook is a rejected candidate, not a
    // contradiction. Only derivations of the deciding strength count, so a
    // defeasible derivation cannot lend its trust to a strict one.
    let rank_of = |ds: &[&Derivation], strict: bool| {
        ds.iter()
            .filter(|d| d.strict() == strict)
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
            a.iter().any(|x| {
                prog.defeats
                    .contains(&(x.source().to_string(), y.source().to_string()))
            })
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
                .all(|y| prog.axes.strictly_within(x.plane(), y.plane()))
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
                    Lit::Atom(a) => {
                        need = need.max(level.get(a.rel.as_str()).copied().unwrap_or(0))
                    }
                    Lit::Agg { over, .. } => {
                        for a in over {
                            need = need.max(level.get(a.rel.as_str()).copied().unwrap_or(0) + 1);
                        }
                    }
                    Lit::Cmp(..) => {}
                }
            }
            let cur = level.entry(r.head.rel.to_string()).or_insert(0);
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

type Binding = BTreeMap<String, Term>;

#[allow(clippy::too_many_arguments)]
fn closure(
    prog: &Program,
    facts: &[&Fact],
    rules: &[&Rule],
    strata: &BTreeMap<String, usize>,
    blocked: &BTreeSet<String>,
    context: &Plane,
    top: usize,
    errors: &mut BTreeSet<String>,
    naive: bool,
) -> (Db, bool) {
    let mut db = Db {
        context: context.clone(),
        ..Db::default()
    };
    for f in facts {
        let key = f.atom.key();
        if blocked.contains(&key) {
            continue;
        }
        let d = make_derivation(
            &db,
            &f.atom,
            &f.id,
            true,
            Strength::Strict,
            f.plane.clone(),
            Box::default(),
            prog.status_rank.get(&f.status).copied().unwrap_or(0),
        );
        let (id, _) = db.insert(&key, || f.atom.clone());
        db.entries[id as usize].1.push(d);
    }
    let limit = db.len() + MAX_ATOMS;
    let mut levels: Vec<usize> = rules
        .iter()
        .map(|r| strata.get(r.head.rel.as_str()).copied().unwrap_or(0))
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
        .map(|n| (n.rel.to_string(), Lazy::build(n, &db)))
        .collect();
    let nests: Vec<&Nesting> = nests
        .into_iter()
        .filter(|n| !lazy.contains_key(n.rel.as_str()))
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
            if fixpoint(&mut db, &layer, blocked, errors, naive, &lazy, limit) {
                settle(&mut db, top);
                return (db, true);
            }
            let mut added = false;
            for n in &here {
                added |= nest(&mut db, n);
            }
            if db.len() > limit {
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
    let pick = |a: &Atom, roles: &(Name, Name)| -> Option<(Term, Term)> {
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
                edges.push((k.to_string(), x, y));
            }
        } else if a.rel == n.rel
            && ds
                .iter()
                .any(|d| d.source() != base_id.as_str() && d.source() != step_id.as_str())
            && let Some((z, y)) = pick(a, &n.roles)
        {
            given.push((k.to_string(), z, y));
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
    // (key, source, premise keys)
    let mut new: Vec<(String, &Name, Vec<String>)> = Vec::new();
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
        new.push((bk, &base_id, vec![ek.clone()]));
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
            new.push((hk, &step_id, vec![ek.clone(), nk.clone()]));
        }
    }
    // Atoms first, then derivations: a premise may be an atom made here.
    for (key, _, _) in &new {
        db.insert(key, || atoms[key].clone());
    }
    let mut added = false;
    for (key, source, premises) in new {
        let ps = premises.iter().map(|k| db.premise(k)).collect();
        let premises = db.premises(ps);
        let d = make_derivation(
            db,
            &atoms[&key],
            source,
            false,
            Strength::Strict,
            Plane::new(),
            premises,
            0,
        );
        let id = db.id(&key).expect("an atom made above");
        added |= db.derive(id, d);
    }
    added
}

/// Premises that are atoms, not absences.
fn real(premises: &[Id]) -> impl Iterator<Item = Id> + '_ {
    premises.iter().copied().filter(|&p| p < ABSENT_ID)
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
    let mut strict = vec![false; db.len()];
    loop {
        let mut grew = false;
        for (k, (_, ds)) in db.entries.iter().enumerate() {
            if !strict[k]
                && ds.iter().any(|d| {
                    d.is_fact || (d.strict() && real(&d.premises).all(|p| strict[p as usize]))
                })
            {
                strict[k] = true;
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    for (_, ds) in db.entries.iter_mut() {
        for d in ds.iter_mut().filter(|d| !d.is_fact) {
            d.evidence.strength = if d.strict() && real(&d.premises).all(|p| strict[p as usize]) {
                Strength::Strict
            } else {
                Strength::Defeasible
            };
        }
    }
    loop {
        let best: Vec<usize> = db
            .entries
            .iter()
            .enumerate()
            .map(|(k, (_, ds))| {
                let s = strict[k];
                let r = ds.iter().filter(|d| d.strict() || !s).map(|d| d.rank).max();
                r.unwrap_or(0)
            })
            .collect();
        let mut changed = false;
        for (_, ds) in db.entries.iter_mut() {
            for d in ds.iter_mut().filter(|d| !d.is_fact) {
                // A strict derivation's premises are all strict atoms.
                let rank = real(&d.premises)
                    .map(|p| best[p as usize])
                    .min()
                    .unwrap_or(top);
                if rank > d.rank {
                    d.rank = rank;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // Effective strength is part of evidence identity. Reattach the settled
    // evidence to the entity; its ID remains fixed by immutable intension.
    for (_, derivations) in &mut db.entries {
        for derivation in derivations {
            derivation.evidence.reidentify();
            derivation.entity = Entity::new(
                derivation.entity.intension.clone(),
                vec![derivation.evidence.id.clone()],
            );
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
    /// node, by its number in `labels` -> its term; a fresh copy `\0y` of a
    /// genus has the genus's term
    terms: Vec<Term>,
    /// (x, genus, edge atom), by x, then by key of the edge atom
    out: Vec<(u32, u32, Id)>,
    /// (z, fresh copy of y, N atom from elsewhere), by z, then by key
    given: Vec<(u32, u32, Id)>,
}

impl Lazy {
    fn build(n: &Nesting, db: &Db) -> Self {
        let pick = |a: &Atom, roles: &(Name, Name)| -> Option<(Term, Term)> {
            let get = |r: &str| a.args.iter().find(|(x, _)| x == r).map(|(_, t)| t.clone());
            Some((get(&roles.0)?, get(&roles.1)?))
        };
        // (atom, x, y) of edges and (atom, z, y) of N atoms, in key order.
        let mut edges: Vec<(Id, Term, Term)> = Vec::new();
        let mut given: Vec<(Id, Term, Term)> = Vec::new();
        for i in db.ids() {
            let a = &db.at(i).0;
            if a.neg {
                continue;
            }
            if a.rel == n.edge
                && let Some((x, y)) = pick(a, &n.edge_roles)
            {
                edges.push((i, x, y));
            } else if a.rel == n.rel
                && let Some((z, y)) = pick(a, &n.roles)
            {
                given.push((i, z, y));
            }
        }
        // Nodes by printed term; a symbol is its own text.
        fn name(t: &Term) -> std::borrow::Cow<'_, str> {
            match t {
                Term::Sym(s) => std::borrow::Cow::Borrowed(s.as_str()),
                t => std::borrow::Cow::Owned(t.to_string()),
            }
        }
        let fresh = |t: &Term| format!("\0{t}");
        let labels = {
            let graph: Vec<(std::borrow::Cow<str>, std::borrow::Cow<str>)> = edges
                .iter()
                .map(|(_, x, y)| (name(x), name(y)))
                .chain(
                    given
                        .iter()
                        .map(|(_, z, y)| (name(z), std::borrow::Cow::Owned(fresh(y)))),
                )
                .collect();
            crate::label::Labels::build(graph.iter().map(|(a, b)| (a.as_ref(), b.as_ref())))
        };
        let node = |s: &str| labels.node(s).expect("a node of the graph");
        let mut terms: Vec<Term> = vec![Term::Sym(Name::default()); labels.len()];
        let mut out: Vec<(u32, u32, Id)> = Vec::with_capacity(edges.len());
        for (e, x, y) in edges {
            let (nx, ny) = (node(&name(&x)), node(&name(&y)));
            out.push((nx, ny, e));
            terms[nx as usize] = x;
            terms[ny as usize] = y;
        }
        let mut from: Vec<(u32, u32, Id)> = Vec::with_capacity(given.len());
        for (k, z, y) in given {
            let (nz, ny) = (node(&name(&z)), node(&fresh(&y)));
            from.push((nz, ny, k));
            terms[nz as usize] = z;
            terms[ny as usize] = y;
        }
        // Stable: within a node, key order stays.
        out.sort_by_key(|&(x, _, _)| x);
        from.sort_by_key(|&(z, _, _)| z);
        Lazy {
            nest: n.clone(),
            labels,
            terms,
            out,
            given: from,
        }
    }

    /// Edges out of a node, or N atoms from elsewhere out of it.
    fn starting(list: &[(u32, u32, Id)], node: Option<u32>) -> &[(u32, u32, Id)] {
        let Some(x) = node else {
            return &[];
        };
        let lo = list.partition_point(|&(a, _, _)| a < x);
        let hi = list.partition_point(|&(a, _, _)| a <= x);
        &list[lo..hi]
    }

    /// Does N(x, y) follow from the edges: a path of edges to y, or of edges
    /// and then a given N atom?
    fn holds(&self, x: &str, y: &str) -> bool {
        self.labels.reaches(x, y) || {
            let qs = Self::starting(&self.out, self.labels.node(x));
            !qs.is_empty() && {
                let fresh = format!("\0{y}");
                qs.iter()
                    .any(|&(_, q, _)| self.labels.within(self.labels.name_at(q), &fresh))
            }
        }
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

    /// The term of a node, or of the genus whose fresh copy it is.
    fn term(&self, s: &str) -> &Term {
        let i = self
            .labels
            .node(s)
            .or_else(|| self.labels.node(&format!("\0{s}")))
            .expect("a node of the nesting");
        &self.terms[i as usize]
    }

    /// The two-role atom N(x, y).
    fn atom(&self, x: &str, y: &str) -> Atom {
        Atom::new(
            self.nest.rel.clone(),
            vec![
                (self.nest.roles.0.clone(), self.term(x).clone()),
                (self.nest.roles.1.clone(), self.term(y).clone()),
            ],
            false,
        )
    }

    /// Makes N(x, y) and every N(z, y) on a path from x to y, each with the
    /// derivations of its two rules.
    /// `up` is everything x is within (`Labels::ancestors`): the cone is
    /// drawn from it, not from everything within y, which for a root of a
    /// whole ontology is the whole ontology.
    fn cone(&self, up: &[&str], y: &str, db: &mut Db) {
        let fresh = format!("\0{y}");
        let mut cone: BTreeSet<&str> = up
            .iter()
            .copied()
            .filter(|z| {
                !z.starts_with('\0') && (self.labels.within(z, y) || self.labels.within(z, &fresh))
            })
            .collect();
        cone.retain(|z| self.holds(z, y));
        // Atoms first: a step rests on the next atom of the cone.
        let made: Vec<(&str, Id)> = cone
            .into_iter()
            .map(|z| {
                let head = self.atom(z, y);
                (z, db.insert(&head.key(), || head).0)
            })
            .collect();
        let (base_id, step_id) = (self.nest.base_id(), self.nest.step_id());
        let fy = self.labels.node(&fresh);
        for (z, id) in made {
            let mut ds: Vec<(&Name, Vec<Id>)> = Vec::new();
            for &(_, q, e) in Self::starting(&self.out, self.labels.node(z)) {
                let q = self.labels.name_at(q);
                if q == y {
                    ds.push((&base_id, vec![e]));
                }
                let mut via: Vec<Id> = Vec::new();
                if self.holds(q, y) {
                    via.push(db.id(&self.atom(q, y).key()).expect("an atom of the cone"));
                }
                via.extend(
                    Self::starting(&self.given, self.labels.node(q))
                        .iter()
                        .filter(|&&(_, w, _)| Some(w) == fy)
                        .map(|&(_, _, k)| k),
                );
                for nk in via {
                    ds.push((&step_id, vec![e, nk]));
                }
            }
            for (source, ps) in ds {
                let premises = db.premises(ps);
                let d = make_derivation(
                    db,
                    &db.at(id).0,
                    source,
                    false,
                    Strength::Strict,
                    Plane::new(),
                    premises,
                    0,
                );
                db.derive(id, d);
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
    limit: usize,
) -> bool {
    // Atoms new in the last round; None in the first round: all are new.
    let mut fresh: Option<BTreeSet<Id>> = None;
    loop {
        let mut added = false;
        let (new, wanted) = {
            let index = Index::new(db, db.ids());
            let delta = fresh
                .as_ref()
                .filter(|_| !naive)
                .map(|f| Index::new(db, db.ids().filter(|i| f.contains(i))));
            let mut new: Vec<(Atom, &Rule, Vec<Pre>)> = Vec::new();
            // (relation, x, y) of lazy atoms that whole matches rest on: a
            // pair the labels gave to a body that did not match makes nothing.
            let mut wanted: BTreeSet<(String, String, String)> = BTreeSet::new();
            for r in rules {
                let mut matches = Vec::new();
                let body = schedule(r);
                let mut ctx = Matcher {
                    db,
                    index: &index,
                    forced: None,
                    lazy,
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
                for (binding, premises) in matches {
                    let head = subst(&r.head, &binding);
                    if head.is_ground() {
                        for p in &premises {
                            if let Pre::Lazy(l) = p {
                                wanted.insert((l.0.clone(), l.1.clone(), l.2.clone()));
                            }
                        }
                        new.push((head, *r, premises));
                    }
                }
            }
            (new, wanted)
        };
        // Atoms of lazy nestings that matches rest on, with their cones. They
        // held already, so they give no new match. Made before the heads, so
        // that the premises can be numbered; no rule here derives them.
        // Sorted by (relation, x): the ancestors of x are found once.
        let mut up: Option<(String, String, Vec<&str>)> = None;
        for (rel, x, y) in &wanted {
            let l = &lazy[rel];
            if up.as_ref().is_none_or(|(r, a, _)| r != rel || a != x) {
                up = Some((rel.clone(), x.clone(), l.labels.ancestors(x)));
            }
            l.cone(&up.as_ref().expect("set above").2, y, db);
        }
        let mut born: BTreeSet<Id> = BTreeSet::new();
        for (head, r, premises) in new {
            let key = head.key();
            if blocked.contains(&key) {
                continue;
            }
            // A body is a conjunction: its premises form a set, not a sequence.
            let ps = premises
                .into_iter()
                .map(|p| match p {
                    Pre::Id(i) => i,
                    Pre::Key(k) => db.premise(&k),
                    Pre::Lazy(l) => db.premise(&l.3),
                })
                .collect();
            let premises = db.premises(ps);
            let conclusion = head.clone();
            let (id, is_new) = db.insert(&key, || head);
            if is_new {
                born.insert(id);
            }
            // The rule's own strength for now; `settle` reads it through the premises.
            let d = make_derivation(
                db,
                &conclusion,
                &r.id,
                false,
                r.strength,
                r.plane.clone(),
                premises,
                0,
            );
            added |= db.derive(id, d);
        }
        if db.len() > limit {
            return true;
        }
        // A new derivation of an old atom gives no new match.
        if !added || (!naive && born.is_empty()) {
            return false;
        }
        fresh = Some(born);
    }
}

/// A premise while a round matches: an atom of the database, the key of an
/// absence, or a lazy atom not made yet: (relation, x, y, key).
#[derive(Clone)]
enum Pre {
    Id(Id),
    Key(String),
    Lazy(Box<(String, String, String, String)>),
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
    by_rel: BTreeMap<(Name, bool), Vec<(Id, &'a Atom)>>,
    by_sym: BTreeMap<SymKey, Vec<(Id, &'a Atom)>>,
}

/// (relation, negated, role, symbol)
type SymKey = (Name, bool, Name, Name);

impl<'a> Index<'a> {
    /// Indexes the atoms `ids` in their order.
    fn new(db: &'a Db, ids: impl Iterator<Item = Id>) -> Self {
        let mut by_rel: BTreeMap<_, Vec<_>> = BTreeMap::new();
        let mut by_sym: BTreeMap<_, Vec<_>> = BTreeMap::new();
        for i in ids {
            let a = &db.at(i).0;
            by_rel
                .entry((a.rel.clone(), a.neg))
                .or_default()
                .push((i, a));
            for (role, t) in &a.args {
                if let Term::Sym(v) = t {
                    by_sym
                        .entry((a.rel.clone(), a.neg, role.clone(), v.clone()))
                        .or_default()
                        .push((i, a));
                }
            }
        }
        Index { by_rel, by_sym }
    }

    /// Atoms that can match `pat` under `binding`: the shortest list among
    /// the roles with a known symbol, else the whole relation. Lists keep
    /// database order, so matching order does not change.
    fn candidates(&self, pat: &Atom, binding: &Binding) -> &[(Id, &'a Atom)] {
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
            let key = (pat.rel.clone(), pat.neg, role.clone(), sym.clone());
            let Some(list) = self.by_sym.get(&key) else {
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
                .get(&(pat.rel.clone(), pat.neg))
                .map_or(&[], Vec::as_slice),
        }
    }
}

struct Matcher<'a> {
    db: &'a Db,
    index: &'a Index<'a>,
    /// The atom literal at this position matches only atoms of this index
    /// (the last round's new atoms).
    forced: Option<(usize, &'a Index<'a>)>,
    /// Lazy nestings by relation; matched from labels, not from the index.
    lazy: &'a BTreeMap<String, Lazy>,
    rule: &'a str,
    errors: &'a mut BTreeSet<String>,
}

impl Matcher<'_> {
    fn body(
        &mut self,
        lits: &[Lit],
        i: usize,
        binding: &mut Binding,
        premises: &mut Vec<Pre>,
        out: &mut Vec<(Binding, Vec<Pre>)>,
    ) {
        if i == lits.len() {
            out.push((binding.clone(), premises.clone()));
            return;
        }
        match &lits[i] {
            Lit::Atom(pat) => {
                let lazy = (!pat.neg)
                    .then(|| self.lazy.get(pat.rel.as_str()))
                    .flatten();
                let found = match (self.forced, lazy) {
                    // A lazy relation does not change within the stratum.
                    (Some((at, _)), Some(_)) if at == i => return,
                    (_, Some(l)) => self.lazy_atom(l, pat, binding),
                    (Some((at, d)), None) if at == i => self.atom_pre(d, pat, binding),
                    _ => self.atom_pre(self.index, pat, binding),
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
    fn lazy_atom(&self, l: &Lazy, pat: &Atom, binding: &Binding) -> Vec<(Binding, Pre)> {
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
                out.push((
                    bind,
                    Pre::Lazy(Box::new((l.nest.rel.to_string(), a, b, key))),
                ));
            }
        }
        out.extend(
            self.atom(self.index, pat, binding)
                .into_iter()
                .filter(|&(_, k)| !seen.contains(self.db.key(k)))
                .map(|(b, k)| (b, Pre::Id(k))),
        );
        out
    }

    fn atom(&self, index: &Index, pat: &Atom, binding: &Binding) -> Vec<(Binding, Id)> {
        let mut out = Vec::new();
        for &(k, ground) in index.candidates(pat, binding) {
            if !fits(pat, ground, binding) {
                continue;
            }
            let mut b = binding.clone();
            if unify(pat, ground, &mut b) {
                out.push((b, k));
            }
        }
        out
    }

    fn atom_pre(&self, index: &Index, pat: &Atom, binding: &Binding) -> Vec<(Binding, Pre)> {
        self.atom(index, pat, binding)
            .into_iter()
            .map(|(b, k)| (b, Pre::Id(k)))
            .collect()
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
    ) -> Option<(Term, Vec<Pre>)> {
        let mut solutions: Vec<(Binding, Vec<Id>)> = vec![(binding.clone(), vec![])];
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
        let mut distinct: BTreeMap<String, (Binding, Vec<Id>)> = BTreeMap::new();
        for (b, used) in solutions {
            let key: Vec<String> = b.iter().map(|(k, v)| format!("{k}={v}")).collect();
            distinct.entry(key.join(";")).or_insert((b, used));
        }
        let mut used_all: Vec<Id> = distinct.values().flat_map(|(_, u)| u.clone()).collect();
        used_all.sort_by(|&a, &b| self.db.key(a).cmp(self.db.key(b)));
        used_all.dedup();
        let mut used_all: Vec<Pre> = used_all.into_iter().map(Pre::Id).collect();
        if distinct.is_empty() {
            // Reasoning from absence must show in the grounds: say what was
            // looked for and not found. Marked with ∅, it is not an atom key.
            let mut looked: Vec<String> =
                over.iter().map(|a| subst(a, binding).to_string()).collect();
            looked.sort();
            used_all = vec![Pre::Key(format!(
                "{ABSENT}none in this context: {}",
                looked.join(", ")
            ))];
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
        .filter(|d| d.source() == source)
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
                out.insert((d.rank, labelled(prog, d.source())));
            }
            stack.extend(db.premise_keys(d).map(str::to_string));
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
fn canonical<'a>(db: &Db, derivs: &'a [Derivation]) -> &'a Derivation {
    let keys = |d: &Derivation| db.premise_keys(d).collect::<Vec<_>>();
    derivs
        .iter()
        .min_by(|a, b| {
            (!a.strict(), !a.is_fact, a.source(), keys(a)).cmp(&(
                !b.strict(),
                !b.is_fact,
                b.source(),
                keys(b),
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
    let d = canonical(&out.db, derivs);
    let kind = if d.is_fact {
        "fact"
    } else if d.strict() {
        "strict"
    } else {
        "defeasible"
    };
    s.push_str(&format!(
        "{pad}{key}  ← {} [{kind}] @ {}\n",
        d.source(),
        plane_to_string(d.plane())
    ));
    if !seen.insert(key.to_string()) || depth > 12 {
        return;
    }
    for p in out.db.premise_keys(d) {
        explain_rec(out, p, depth + 1, seen, s);
    }
}

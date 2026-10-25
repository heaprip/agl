//! Concepts by definition: unfolding to primitives, comparison, common genus.
//!
//! A sense of a concept is a conjunctive query with inequalities: the head
//! roles are its free variables, the body its atoms and `?a != ?b`. Unfolding
//! replaces each concept atom by the senses of that concept, down to relations
//! that are not concepts — the primitives. Comparison is containment of unions
//! of such queries (Chandra and Merlin, 1977; with inequalities, Klug, 1988):
//! `A ⊑ B` when, whatever the facts, every answer of A is an answer of B. It
//! is decided on the canonical worlds of each sense of A, one world per way of
//! identifying its variables that its inequalities allow.
//!
//! Planes. A sense is visible in a context within its plane, as a rule is.
//! Primitives are read through planes too: a narrower context sees more facts,
//! so an atom of B read in context `c2` can match an atom of A read in `c1`
//! only when `c2` lies within `c1`.
//!
//! The common genus of two concepts is their least general generalization
//! (Plotkin, 1970): the product of the two queries, reduced to its core.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::eval;
use crate::model::*;

/// A variable or a constant of a query.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum T {
    V(String),
    C(String),
}

impl T {
    fn of(t: &Term) -> T {
        match t {
            Term::Var(v) => T::V(v.clone()),
            other => T::C(other.to_string()),
        }
    }
}

impl fmt::Display for T {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            T::V(v) => write!(f, "?{v}"),
            T::C(c) => write!(f, "{c}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CAtom {
    pub rel: String,
    pub args: Vec<(String, T)>,
}

/// One sense: a conjunctive query with inequalities.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cq {
    pub head: Vec<(String, T)>,
    pub atoms: Vec<CAtom>,
    pub neqs: Vec<(T, T)>,
}

impl fmt::Display for Cq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut parts: Vec<String> = self
            .atoms
            .iter()
            .map(|a| {
                let args: Vec<String> = a.args.iter().map(|(r, t)| format!("{r}: {t}")).collect();
                format!("{}({})", a.rel, args.join(", "))
            })
            .collect();
        parts.extend(self.neqs.iter().map(|(l, r)| format!("{l} != {r}")));
        write!(f, "{}", parts.join(", "))
    }
}

impl Cq {
    fn roles(&self) -> Vec<&str> {
        self.head.iter().map(|(r, _)| r.as_str()).collect()
    }

    /// Variables in order of first appearance: head, atoms, inequalities.
    fn vars(&self) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let terms = self
            .head
            .iter()
            .map(|(_, t)| t)
            .chain(
                self.atoms
                    .iter()
                    .flat_map(|a| a.args.iter().map(|(_, t)| t)),
            )
            .chain(self.neqs.iter().flat_map(|(l, r)| [l, r]));
        for t in terms {
            if let T::V(v) = t
                && !out.contains(v)
            {
                out.push(v.clone());
            }
        }
        out
    }

    fn consts(&self) -> BTreeSet<String> {
        let terms = self
            .head
            .iter()
            .map(|(_, t)| t)
            .chain(
                self.atoms
                    .iter()
                    .flat_map(|a| a.args.iter().map(|(_, t)| t)),
            )
            .chain(self.neqs.iter().flat_map(|(l, r)| [l, r]));
        terms
            .filter_map(|t| match t {
                T::C(c) => Some(c.clone()),
                T::V(_) => None,
            })
            .collect()
    }

    fn subst(&self, map: &BTreeMap<String, T>) -> Cq {
        let s = |t: &T| match t {
            T::V(v) => map.get(v).cloned().unwrap_or_else(|| t.clone()),
            c => c.clone(),
        };
        Cq {
            head: self.head.iter().map(|(r, t)| (r.clone(), s(t))).collect(),
            atoms: self
                .atoms
                .iter()
                .map(|a| CAtom {
                    rel: a.rel.clone(),
                    args: a.args.iter().map(|(r, t)| (r.clone(), s(t))).collect(),
                })
                .collect(),
            neqs: self.neqs.iter().map(|(l, r)| (s(l), s(r))).collect(),
        }
    }

    /// The same query whatever the order of its atoms: head variables named
    /// after their roles, the rest `?x1`, `?x2`… in the naming that gives the
    /// smallest text, atoms and inequalities sorted and without repeats. The
    /// prefix `x` grows (`x_`, `x__`…) until no role is called like a numbered
    /// variable, so a role `x1` cannot merge with another variable. With more
    /// than `MAX_CANON` other variables, they are named in order of appearance
    /// in the atoms sorted as written: still independent of the order of the
    /// atoms, though not of the names of the variables.
    pub fn canonical(&self) -> Cq {
        let mut map = BTreeMap::new();
        for (role, t) in &self.head {
            if let T::V(v) = t {
                map.entry(v.clone()).or_insert_with(|| T::V(role.clone()));
            }
        }
        let mut prefix = "x".to_string();
        let numbered = |role: &str, prefix: &str| {
            role.strip_prefix(prefix)
                .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
        };
        while self.head.iter().any(|(role, _)| numbered(role, &prefix)) {
            prefix.push('_');
        }
        let rest: Vec<String> = if self.vars().len() - map.len() <= MAX_CANON {
            self.vars()
        } else {
            self.clone().sorted().vars()
        }
        .into_iter()
        .filter(|v| !map.contains_key(v))
        .collect();
        let named = |order: &[usize]| {
            let mut m = map.clone();
            for (k, &i) in order.iter().enumerate() {
                m.insert(rest[i].clone(), T::V(format!("{prefix}{}", k + 1)));
            }
            self.subst(&m).sorted()
        };
        let order: Vec<usize> = (0..rest.len()).collect();
        if rest.len() > MAX_CANON {
            return named(&order);
        }
        let best = named(&self.least_naming(&map, &rest, &prefix));
        #[cfg(debug_assertions)]
        {
            // The plain search this one replaces: build, sort and print every naming.
            let mut order = order;
            let mut slow = named(&order);
            let mut slow_text = slow.to_string();
            while next_permutation(&mut order) {
                let q = named(&order);
                let text = q.to_string();
                if text < slow_text {
                    slow = q;
                    slow_text = text;
                }
            }
            debug_assert_eq!(best, slow, "canonical naming of {self}");
        }
        best
    }

    /// The order of `rest` whose naming `prefix1`, `prefix2`… gives the
    /// smallest text of the sorted query; the first such order among the
    /// permutations in lexicographic order. Same result as building, sorting
    /// and printing the query for every naming, without the copies: atoms are
    /// cut once into roles and slots, each naming only fills the slots.
    fn least_naming<'a>(
        &'a self,
        map: &'a BTreeMap<String, T>,
        rest: &[String],
        prefix: &str,
    ) -> Vec<usize> {
        /// A term as `T` orders it: variables before constants, then by name.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum View<'a> {
            V(&'a str),
            C(&'a str),
        }
        enum Slot<'a> {
            Fixed(View<'a>),
            Rest(usize),
        }
        let slot = |t: &'a T| -> Slot<'a> {
            match t {
                T::C(c) => Slot::Fixed(View::C(c)),
                T::V(v) => match rest.iter().position(|x| x == v) {
                    Some(i) => Slot::Rest(i),
                    None => match map.get(v) {
                        Some(T::V(n)) => Slot::Fixed(View::V(n)),
                        Some(T::C(c)) => Slot::Fixed(View::C(c)),
                        None => Slot::Fixed(View::V(v)),
                    },
                },
            }
        };
        let atoms: Vec<(&str, Vec<(&str, Slot)>)> = self
            .atoms
            .iter()
            .map(|a| {
                (
                    a.rel.as_str(),
                    a.args.iter().map(|(r, t)| (r.as_str(), slot(t))).collect(),
                )
            })
            .collect();
        let neqs: Vec<(Slot, Slot)> = self.neqs.iter().map(|(l, r)| (slot(l), slot(r))).collect();
        let names: Vec<String> = (1..=rest.len()).map(|k| format!("{prefix}{k}")).collect();
        let mut name_of = vec![0usize; rest.len()];
        let mut order: Vec<usize> = (0..rest.len()).collect();
        let mut best_order = order.clone();
        let mut best_text: Option<String> = None;
        let mut text = String::new();
        let mut sorted_atoms: Vec<(&str, Vec<(&str, View)>)> = Vec::with_capacity(atoms.len());
        let mut sorted_neqs: Vec<(View, View)> = Vec::with_capacity(neqs.len());
        loop {
            for (k, &i) in order.iter().enumerate() {
                name_of[i] = k;
            }
            fn view<'n>(s: &Slot<'n>, names: &'n [String], name_of: &[usize]) -> View<'n> {
                match s {
                    Slot::Fixed(v) => *v,
                    Slot::Rest(i) => View::V(&names[name_of[*i]]),
                }
            }
            let view = |s| view(s, &names, &name_of);
            sorted_atoms.clear();
            for (rel, args) in &atoms {
                sorted_atoms.push((rel, args.iter().map(|(r, s)| (*r, view(s))).collect()));
            }
            sorted_atoms.sort();
            sorted_atoms.dedup();
            sorted_neqs.clear();
            for (l, r) in &neqs {
                let (l, r) = (view(l), view(r));
                sorted_neqs.push(if r < l { (r, l) } else { (l, r) });
            }
            sorted_neqs.sort();
            sorted_neqs.dedup();
            text.clear();
            let term = |text: &mut String, v: &View| match v {
                View::V(n) => {
                    text.push('?');
                    text.push_str(n);
                }
                View::C(c) => text.push_str(c),
            };
            let mut first = true;
            for (rel, args) in &sorted_atoms {
                if !first {
                    text.push_str(", ");
                }
                first = false;
                text.push_str(rel);
                text.push('(');
                for (j, (role, v)) in args.iter().enumerate() {
                    if j > 0 {
                        text.push_str(", ");
                    }
                    text.push_str(role);
                    text.push_str(": ");
                    term(&mut text, v);
                }
                text.push(')');
            }
            for (l, r) in &sorted_neqs {
                if !first {
                    text.push_str(", ");
                }
                first = false;
                term(&mut text, l);
                text.push_str(" != ");
                term(&mut text, r);
            }
            if best_text.as_ref().is_none_or(|b| text < *b) {
                best_text = Some(text.clone());
                best_order.copy_from_slice(&order);
            }
            if !next_permutation(&mut order) {
                return best_order;
            }
        }
    }

    fn sorted(mut self) -> Cq {
        self.atoms.sort();
        self.atoms.dedup();
        for (l, r) in &mut self.neqs {
            if r < l {
                std::mem::swap(l, r);
            }
        }
        self.neqs.sort();
        self.neqs.dedup();
        self
    }

    fn unsatisfiable(&self) -> bool {
        self.neqs.iter().any(|(l, r)| l == r)
    }
}

/// Beyond this many variables outside the head, naming is not minimized.
const MAX_CANON: usize = 7;

fn next_permutation(xs: &mut [usize]) -> bool {
    let Some(i) = (1..xs.len()).rev().find(|&i| xs[i - 1] < xs[i]) else {
        return false;
    };
    let j = (i..xs.len()).rev().find(|&j| xs[j] > xs[i - 1]).unwrap();
    xs.swap(i - 1, j);
    xs[i..].reverse();
    true
}

/// One sense as written, without unfolding, in canonical form: a key that does
/// not depend on the order of the body.
pub fn sense_key(c: &Concept) -> String {
    let t = |t: &Term| T::of(t);
    let mut q = Cq {
        head: c
            .head
            .args
            .iter()
            .map(|(r, x)| (r.to_string(), t(x)))
            .collect(),
        atoms: vec![],
        neqs: vec![],
    };
    for lit in &c.body {
        match lit {
            Lit::Atom(a) => q.atoms.push(CAtom {
                rel: a.rel.to_string(),
                args: a.args.iter().map(|(r, x)| (r.to_string(), t(x))).collect(),
            }),
            Lit::Cmp(Expr::Term(l), CmpOp::Ne, Expr::Term(r)) => q.neqs.push((t(l), t(r))),
            _ => {}
        }
    }
    format!(
        "{} @ {} : {}",
        c.head.rel,
        plane_to_string(&c.plane),
        q.canonical()
    )
}

pub fn is_concept(prog: &Program, name: &str) -> bool {
    prog.concepts.iter().any(|c| c.head.rel == name)
}

fn senses<'a>(prog: &'a Program, name: &str, plane: &Plane) -> Vec<&'a Concept> {
    let mut out: Vec<&Concept> = prog
        .concepts
        .iter()
        .filter(|c| c.head.rel == name && prog.axes.plane_within(plane, &c.plane))
        .collect();
    out.sort_by_cached_key(|c| sense_key(c));
    out
}

struct Unfolder<'a> {
    prog: &'a Program,
    plane: &'a Plane,
    fresh: usize,
    stack: Vec<String>,
}

impl Unfolder<'_> {
    /// The senses of `name`, with concept atoms expanded `depth` levels down.
    fn concept(&mut self, name: &str, depth: usize) -> Result<Vec<Cq>, String> {
        if self.stack.iter().any(|s| s == name) {
            return Err(format!(
                "concept `{name}` is defined through itself: {} -> {name}",
                self.stack.join(" -> ")
            ));
        }
        let senses = senses(self.prog, name, self.plane);
        if senses.is_empty() {
            return Err(format!(
                "concept `{name}` has no sense in {}",
                plane_to_string(self.plane)
            ));
        }
        self.stack.push(name.to_string());
        let mut out = Vec::new();
        for c in senses {
            out.extend(self.sense(c, depth)?);
        }
        self.stack.pop();
        Ok(out)
    }

    fn sense(&mut self, c: &Concept, depth: usize) -> Result<Vec<Cq>, String> {
        self.fresh += 1;
        let tag = self.fresh;
        let rn = |t: &Term| match t {
            Term::Var(v) => T::V(format!("{v}#{tag}")),
            other => T::of(other),
        };
        let head = c
            .head
            .args
            .iter()
            .map(|(r, t)| (r.to_string(), rn(t)))
            .collect();
        let mut partial = vec![Cq {
            head,
            atoms: vec![],
            neqs: vec![],
        }];
        for lit in &c.body {
            match lit {
                Lit::Atom(a) => {
                    let atom = CAtom {
                        rel: a.rel.to_string(),
                        args: a.args.iter().map(|(r, t)| (r.to_string(), rn(t))).collect(),
                    };
                    if depth > 0 && is_concept(self.prog, &a.rel) {
                        let subs = self.concept(&a.rel, depth - 1)?;
                        let mut next = Vec::new();
                        for p in &partial {
                            for s in &subs {
                                next.push(inline(p, &atom, s)?);
                            }
                        }
                        partial = next;
                    } else {
                        partial.iter_mut().for_each(|p| p.atoms.push(atom.clone()));
                    }
                }
                Lit::Cmp(Expr::Term(l), CmpOp::Ne, Expr::Term(r)) => {
                    partial.iter_mut().for_each(|p| p.neqs.push((rn(l), rn(r))));
                }
                other => return Err(format!("not a concept literal: `{other}`")),
            }
        }
        Ok(partial)
    }
}

/// `p` with the concept atom `atom` replaced by the sense `s`.
fn inline(p: &Cq, atom: &CAtom, s: &Cq) -> Result<Cq, String> {
    let mut map = BTreeMap::new();
    for (role, t) in &atom.args {
        let Some((_, T::V(v))) = s.head.iter().find(|(r, _)| r == role) else {
            return Err(format!("concept `{}` has no role `{role}`", atom.rel));
        };
        map.insert(v.clone(), t.clone());
    }
    let s = s.subst(&map);
    let mut out = p.clone();
    out.atoms.extend(s.atoms);
    out.neqs.extend(s.neqs);
    Ok(out)
}

/// The senses of a concept in `plane`, expanded `depth` levels down
/// (`usize::MAX`: to primitives), in canonical form.
pub fn unfold(prog: &Program, name: &str, plane: &Plane, depth: usize) -> Result<Vec<Cq>, String> {
    let mut u = Unfolder {
        prog,
        plane,
        fresh: 0,
        stack: vec![],
    };
    let mut out: Vec<Cq> = u
        .concept(name, depth)?
        .iter()
        .map(Cq::canonical)
        .filter(|q| !q.unsatisfiable())
        .collect();
    out.sort_by_key(|q| q.to_string());
    out.dedup();
    Ok(out)
}

/// An element of a canonical world: a block of identified variables, or a
/// constant.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum E {
    B(usize),
    C(String),
}

struct World {
    atoms: BTreeSet<(String, Vec<(String, E)>)>,
    head: Vec<(String, E)>,
}

/// Beyond this many variables the worlds are not enumerated.
const MAX_VARS: usize = 8;

/// The canonical worlds of `q`. With `all`, one per identification of its
/// variables (and of variables with constants) that its inequalities allow;
/// otherwise only the world where all variables differ.
fn worlds(q: &Cq, consts: &BTreeSet<String>, all: bool) -> Result<Vec<World>, String> {
    let vars = q.vars();
    if all && vars.len() > MAX_VARS {
        return Err(format!(
            "{} variables: too many to compare (at most {MAX_VARS})",
            vars.len()
        ));
    }
    let consts: Vec<&String> = consts.iter().collect();
    let mut out = Vec::new();
    let mut blocks = vec![0usize; vars.len()];
    let mut assign: Vec<Option<usize>> = Vec::new();
    partitions(&mut blocks, 0, 0, all, &mut |blocks, k| {
        let choices = if all { consts.len() + 1 } else { 1 };
        assign.clear();
        assign.resize(k, None);
        loop {
            let used: Vec<usize> = assign.iter().flatten().copied().collect();
            let distinct = used.iter().collect::<BTreeSet<_>>().len() == used.len();
            if distinct {
                let elem = |t: &T| match t {
                    T::C(c) => E::C(c.clone()),
                    T::V(v) => {
                        let i = vars.iter().position(|x| x == v).unwrap();
                        match assign[blocks[i]] {
                            Some(c) => E::C(consts[c].clone()),
                            None => E::B(blocks[i]),
                        }
                    }
                };
                if q.neqs.iter().all(|(l, r)| elem(l) != elem(r)) {
                    out.push(World {
                        atoms: q
                            .atoms
                            .iter()
                            .map(|a| {
                                let args = a.args.iter().map(|(r, t)| (r.clone(), elem(t)));
                                (a.rel.clone(), args.collect())
                            })
                            .collect(),
                        head: q.head.iter().map(|(r, t)| (r.clone(), elem(t))).collect(),
                    });
                }
            }
            // Next assignment of blocks to constants, as a counter in base `choices`.
            let mut i = 0;
            loop {
                if i == k {
                    return;
                }
                let next = assign[i].map_or(0, |c| c + 1);
                if next < choices - 1 {
                    assign[i] = Some(next);
                    break;
                }
                assign[i] = None;
                i += 1;
            }
        }
    });
    Ok(out)
}

/// Set partitions as restricted growth strings; `all = false` gives only the
/// finest one.
fn partitions(
    blocks: &mut Vec<usize>,
    i: usize,
    k: usize,
    all: bool,
    visit: &mut dyn FnMut(&[usize], usize),
) {
    if i == blocks.len() {
        visit(blocks, k);
        return;
    }
    if all {
        for b in 0..k {
            blocks[i] = b;
            partitions(blocks, i + 1, k, all, visit);
        }
    }
    blocks[i] = k;
    partitions(blocks, i + 1, k + 1, all, visit);
}

/// Atoms of `q` in search order: each next atom shares the most variables
/// with the head and the atoms before it.
fn search_order(q: &Cq) -> Vec<&CAtom> {
    let mut bound: BTreeSet<&T> = q.head.iter().map(|(_, t)| t).collect();
    let mut left: Vec<&CAtom> = q.atoms.iter().collect();
    let mut out = Vec::new();
    while !left.is_empty() {
        let score = |a: &CAtom| {
            a.args
                .iter()
                .filter(|(_, t)| matches!(t, T::C(_)) || bound.contains(t))
                .count()
        };
        let best = (0..left.len())
            .max_by_key(|&i| (score(left[i]), std::cmp::Reverse(i)))
            .unwrap();
        let a = left.remove(best);
        bound.extend(a.args.iter().map(|(_, t)| t));
        out.push(a);
    }
    out
}

/// A homomorphism from `q` into the world that sends its head to the world's.
/// `order` is `search_order(q)`, computed once per query.
fn hom<'a>(q: &'a Cq, order: &[&'a CAtom], w: &World, link: bool) -> bool {
    let mut b: BTreeMap<&str, E> = BTreeMap::new();
    for (role, t) in &q.head {
        let Some((_, e)) = w.head.iter().find(|(r, _)| r == role) else {
            return false;
        };
        if !bind(&mut b, t, e) {
            return false;
        }
    }
    if !link && !q.atoms.is_empty() {
        return false;
    }
    let mut by_rel: BTreeMap<&str, Vec<&Vec<(String, E)>>> = BTreeMap::new();
    for (rel, args) in &w.atoms {
        by_rel.entry(rel.as_str()).or_default().push(args);
    }
    go(q, order, &by_rel, 0, &mut b)
}

fn bind<'a>(b: &mut BTreeMap<&'a str, E>, t: &'a T, e: &E) -> bool {
    match t {
        T::C(c) => matches!(e, E::C(x) if x == c),
        T::V(v) => match b.get(v.as_str()) {
            Some(x) => x == e,
            None => {
                b.insert(v, e.clone());
                true
            }
        },
    }
}

fn go<'a>(
    q: &'a Cq,
    order: &[&'a CAtom],
    by_rel: &BTreeMap<&str, Vec<&Vec<(String, E)>>>,
    i: usize,
    b: &mut BTreeMap<&'a str, E>,
) -> bool {
    if i == order.len() {
        return q.neqs.iter().all(|(l, r)| {
            let get = |t: &T| match t {
                T::C(c) => Some(E::C(c.clone())),
                T::V(v) => b.get(v.as_str()).cloned(),
            };
            match (get(l), get(r)) {
                (Some(x), Some(y)) => x != y,
                // An unbound variable takes a fresh element.
                _ => l != r,
            }
        });
    }
    let a = order[i];
    let Some(cands) = by_rel.get(a.rel.as_str()) else {
        return false;
    };
    for args in cands {
        let mut added: Vec<&str> = Vec::new();
        let mut fits = true;
        for (role, t) in &a.args {
            let Some((_, e)) = args.iter().find(|(r, _)| r == role) else {
                fits = false;
                break;
            };
            if let T::V(v) = t
                && !b.contains_key(v.as_str())
            {
                b.insert(v, e.clone());
                added.push(v);
            } else if !bind(b, t, e) {
                fits = false;
                break;
            }
        }
        if fits && go(q, order, by_rel, i + 1, b) {
            return true;
        }
        for v in added {
            b.remove(v);
        }
    }
    false
}

/// A completion of `w` by the covers where no sense of `u2` holds, if there is
/// one. Each element in none of a cover's alternatives may be in any of them.
/// Adding atoms never breaks a match, so a branch stops as soon as `u2` holds.
fn uncovered(
    w: &World,
    covers: &[&Vec<(String, String)>],
    holds: &dyn Fn(&World) -> bool,
) -> Option<World> {
    if holds(w) {
        return None;
    }
    let mut elems: BTreeSet<E> = w.head.iter().map(|(_, e)| e.clone()).collect();
    for (_, args) in &w.atoms {
        elems.extend(args.iter().map(|(_, e)| e.clone()));
    }
    for cover in covers {
        for e in &elems {
            let has = cover.iter().any(|(rel, role)| {
                w.atoms
                    .iter()
                    .any(|(r, args)| r == rel && args.iter().any(|(x, y)| x == role && y == e))
            });
            if has {
                continue;
            }
            for (rel, role) in cover.iter() {
                let mut atoms = w.atoms.clone();
                atoms.insert((rel.clone(), vec![(role.clone(), e.clone())]));
                let next = World {
                    atoms,
                    head: w.head.clone(),
                };
                if let Some(cx) = uncovered(&next, covers, holds) {
                    return Some(cx);
                }
            }
            return None;
        }
    }
    Some(World {
        atoms: w.atoms.clone(),
        head: w.head.clone(),
    })
}

/// Every answer of `q1` read in `c1` is an answer of the union `u2` read in `c2`.
fn contained(prog: &Program, q1: &Cq, c1: &Plane, u2: &[Cq], c2: &Plane) -> Result<bool, String> {
    Ok(counterexample(prog, q1, c1, u2, c2)?.is_none())
}

impl World {
    fn name(&self, e: &E) -> String {
        match e {
            E::C(c) => c.clone(),
            E::B(i) => match self.head.iter().find(|(_, x)| x == e) {
                Some((role, _)) => role.clone(),
                None => format!("_{i}"),
            },
        }
    }
}

impl fmt::Display for World {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let atoms: Vec<String> = self
            .atoms
            .iter()
            .map(|(rel, args)| {
                let args: Vec<String> = args
                    .iter()
                    .map(|(r, e)| format!("{r}: {}", self.name(e)))
                    .collect();
                format!("{rel}({})", args.join(", "))
            })
            .collect();
        let same: Vec<String> = self
            .head
            .iter()
            .enumerate()
            .flat_map(|(i, (r, e))| {
                self.head[i + 1..]
                    .iter()
                    .filter(move |(_, x)| x == e)
                    .map(move |(r2, _)| format!("{r} = {r2}"))
            })
            .collect();
        write!(f, "{}", atoms.join(", "))?;
        if !same.is_empty() {
            write!(f, "; {}", same.join(", "))?;
        }
        Ok(())
    }
}

/// A canonical world of `q1`, completed by the covers, where `u2` does not
/// hold, if there is one.
fn counterexample(
    prog: &Program,
    q1: &Cq,
    c1: &Plane,
    u2: &[Cq],
    c2: &Plane,
) -> Result<Option<World>, String> {
    let link = prog.axes.plane_within(c2, c1);
    let all = u2.iter().any(|q| !q.neqs.is_empty());
    let mut consts = q1.consts();
    u2.iter().for_each(|q| consts.extend(q.consts()));
    let rels: BTreeSet<&str> = u2
        .iter()
        .flat_map(|q| q.atoms.iter().map(|a| a.rel.as_str()))
        .collect();
    // Canonical order, so the counterexample found does not depend on the
    // order of statements.
    let mut covers: Vec<Vec<(String, String)>> = prog
        .covers
        .iter()
        .filter(|c| c.iter().any(|(r, _)| rels.contains(r.as_str())))
        .map(|c| {
            let mut c = c.clone();
            c.sort();
            c
        })
        .collect();
    covers.sort();
    let covers: Vec<&Vec<(String, String)>> = covers.iter().collect();
    let roles = q1.roles();
    let targets: Vec<(&Cq, Vec<&CAtom>)> = u2
        .iter()
        .filter(|q2| q2.roles() == roles)
        .map(|q2| (q2, search_order(q2)))
        .collect();
    let holds = |w: &World| targets.iter().any(|(q2, order)| hom(q2, order, w, link));
    for w in worlds(q1, &consts, all)? {
        if let Some(cx) = uncovered(&w, &covers, &holds) {
            return Ok(Some(cx));
        }
    }
    Ok(None)
}

fn union_counterexample(
    prog: &Program,
    u1: &[Cq],
    c1: &Plane,
    u2: &[Cq],
    c2: &Plane,
) -> Result<Option<World>, String> {
    for q in u1 {
        if let Some(w) = counterexample(prog, q, c1, u2, c2)? {
            return Ok(Some(w));
        }
    }
    Ok(None)
}

pub fn union_contained(
    prog: &Program,
    u1: &[Cq],
    c1: &Plane,
    u2: &[Cq],
    c2: &Plane,
) -> Result<bool, String> {
    for q in u1 {
        if !contained(prog, q, c1, u2, c2)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The query without redundant atoms and inequalities: its core.
fn core(prog: &Program, q: &Cq, plane: &Plane) -> Result<Cq, String> {
    let mut q = q.clone();
    let mut i = 0;
    while i < q.atoms.len() {
        let mut r = q.clone();
        r.atoms.remove(i);
        if contained(prog, &r, plane, std::slice::from_ref(&q), plane)? {
            q = r;
        } else {
            i += 1;
        }
    }
    let mut i = 0;
    while i < q.neqs.len() {
        let mut r = q.clone();
        r.neqs.remove(i);
        if contained(prog, &r, plane, std::slice::from_ref(&q), plane)? {
            q = r;
        } else {
            i += 1;
        }
    }
    Ok(q.canonical())
}

/// Cores of the senses, without senses that another sense covers, sorted.
pub fn minimize(prog: &Program, u: &[Cq], plane: &Plane) -> Result<Vec<Cq>, String> {
    let mut cores = Vec::new();
    for q in u {
        cores.push(core(prog, q, plane)?);
    }
    cores.sort_by_key(|q| q.to_string());
    cores.dedup();
    let mut out: Vec<Cq> = Vec::new();
    for (i, q) in cores.iter().enumerate() {
        let mut covered = false;
        for (j, r) in cores.iter().enumerate() {
            if i != j
                && contained(prog, q, plane, std::slice::from_ref(r), plane)?
                && !(j > i && contained(prog, r, plane, std::slice::from_ref(q), plane)?)
            {
                covered = true;
                break;
            }
        }
        if !covered {
            out.push(q.clone());
        }
    }
    Ok(out)
}

/// The concept down to primitives, minimized.
pub fn normal_form(prog: &Program, name: &str, plane: &Plane) -> Result<Vec<Cq>, String> {
    minimize(prog, &unfold(prog, name, plane, usize::MAX)?, plane)
}

/// The least general generalization of two senses: their product, reduced to
/// its core. `None` when it constrains no head role.
pub fn common(prog: &Program, q1: &Cq, q2: &Cq, plane: &Plane) -> Result<Option<Cq>, String> {
    if q1.roles() != q2.roles() {
        return Ok(None);
    }
    let pair = |a: &T, b: &T| match (a, b) {
        (T::C(x), T::C(y)) if x == y => a.clone(),
        _ => T::V(format!("{a}|{b}")),
    };
    let head = q1
        .head
        .iter()
        .zip(&q2.head)
        .map(|((r, a), (_, b))| (r.clone(), pair(a, b)))
        .collect();
    let mut atoms = Vec::new();
    for a1 in &q1.atoms {
        for a2 in q2.atoms.iter().filter(|a| a.rel == a1.rel) {
            let args: Vec<(String, T)> = a1
                .args
                .iter()
                .filter_map(|(r, t1)| {
                    let (_, t2) = a2.args.iter().find(|(r2, _)| r2 == r)?;
                    Some((r.clone(), pair(t1, t2)))
                })
                .collect();
            if !args.is_empty() {
                atoms.push(CAtom {
                    rel: a1.rel.clone(),
                    args,
                });
            }
        }
    }
    let mut neqs = Vec::new();
    for (l1, r1) in &q1.neqs {
        for (l2, r2) in &q2.neqs {
            neqs.push((pair(l1, l2), pair(r1, r2)));
            neqs.push((pair(l1, r2), pair(r1, l2)));
        }
    }
    let product = Cq { head, atoms, neqs };
    let used: Vec<String> = Cq {
        head: product.head.clone(),
        atoms: product.atoms.clone(),
        neqs: vec![],
    }
    .vars();
    let mut product = product;
    product.neqs.retain(|(l, r)| {
        [l, r]
            .iter()
            .all(|t| matches!(t, T::V(v) if used.contains(v)) || matches!(t, T::C(_)))
    });
    // Variables that touch no head role are dropped with their atoms: the
    // genus is about the two people, not about unrelated others.
    let product = connected(&product);
    let g = core(prog, &product.canonical(), plane)?;
    if !links_head(&g) {
        return Ok(None);
    }
    let covers = contained(prog, q1, plane, std::slice::from_ref(&g), plane)?
        && contained(prog, q2, plane, std::slice::from_ref(&g), plane)?;
    if !covers {
        return Err(format!(
            "common genus `{g}` does not cover `{q1}` and `{q2}`"
        ));
    }
    Ok(Some(g))
}

/// The atoms join all head roles into one structure: the genus says how the
/// two people are related, not only what each of them is.
fn links_head(q: &Cq) -> bool {
    let heads: Vec<&T> = q.head.iter().map(|(_, t)| t).collect();
    let Some(first) = heads.first() else {
        return false;
    };
    let mut reach: BTreeSet<&T> = BTreeSet::from([*first]);
    loop {
        let mut grew = false;
        for a in &q.atoms {
            if a.args.iter().any(|(_, t)| reach.contains(t)) {
                for (_, t) in &a.args {
                    grew |= matches!(t, T::V(_)) && reach.insert(t);
                }
            }
        }
        if !grew {
            break;
        }
    }
    heads.iter().all(|h| reach.contains(h))
}

/// Only atoms connected to a head variable through shared variables.
fn connected(q: &Cq) -> Cq {
    let mut reach: BTreeSet<T> = q.head.iter().map(|(_, t)| t.clone()).collect();
    let mut keep = vec![false; q.atoms.len()];
    loop {
        let mut grew = false;
        for (i, a) in q.atoms.iter().enumerate() {
            if !keep[i]
                && a.args
                    .iter()
                    .any(|(_, t)| matches!(t, T::V(_)) && reach.contains(t))
            {
                keep[i] = true;
                grew = true;
                reach.extend(a.args.iter().map(|(_, t)| t.clone()));
            }
        }
        if !grew {
            break;
        }
    }
    Cq {
        head: q.head.clone(),
        atoms: q
            .atoms
            .iter()
            .zip(&keep)
            .filter(|(_, k)| **k)
            .map(|(a, _)| a.clone())
            .collect(),
        neqs: q
            .neqs
            .iter()
            .filter(|(l, r)| reach.contains(l) && reach.contains(r))
            .cloned()
            .collect(),
    }
}

/// Relations the rules for `rel` rest on, `rel` included.
fn cone(prog: &Program, rel: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::from([rel.to_string()]);
    loop {
        let before = out.len();
        let mut body: Vec<String> = Vec::new();
        for r in prog
            .rules
            .iter()
            .filter(|r| out.contains(r.head.rel.as_str()))
        {
            for lit in &r.body {
                match lit {
                    Lit::Atom(a) => body.push(a.rel.to_string()),
                    Lit::Agg { over, .. } => body.extend(over.iter().map(|a| a.rel.to_string())),
                    Lit::Cmp(..) => {}
                }
            }
        }
        out.extend(body);
        if out.len() == before {
            return out;
        }
    }
}

/// Why the rules for the relations in `cone` are not monotone, if they are
/// not. Canonical worlds decide containment exactly for strict rules over
/// positive atoms and `=`/`!=` between symbols; aggregates, ordering,
/// arithmetic, defeasible rules and negation can each make a larger world
/// lose a conclusion.
fn not_monotone(prog: &Program, cone: &BTreeSet<String>) -> Option<String> {
    for r in prog
        .rules
        .iter()
        .filter(|r| cone.contains(r.head.rel.as_str()))
    {
        let why = if r.strength == Strength::Defeasible {
            Some("is defeasible")
        } else if r.head.neg {
            Some("derives a negation")
        } else {
            r.body.iter().find_map(|lit| match lit {
                Lit::Atom(a) if a.neg => Some("has a negated premise"),
                Lit::Agg { .. } => Some("aggregates"),
                Lit::Cmp(Expr::Term(l), CmpOp::Eq | CmpOp::Ne, Expr::Term(r))
                    if !matches!(l, Term::Num(..)) && !matches!(r, Term::Num(..)) =>
                {
                    None
                }
                Lit::Cmp(..) => Some("compares or computes"),
                Lit::Atom(_) => None,
            })
        };
        if let Some(why) = why {
            return Some(format!("rule `{}` {why}", r.id));
        }
    }
    None
}

/// Symbols the rules for `cone` and the `forbid` constraints mention: a
/// canonical world must be able to name them, or a rule like `?a != adam`
/// is never tested on `adam`.
fn rule_consts(prog: &Program, cone: &BTreeSet<String>) -> BTreeSet<String> {
    fn sym(t: &Term, out: &mut BTreeSet<String>) {
        if let Term::Sym(s) = t {
            out.insert(s.to_string());
        }
    }
    fn expr(e: &Expr, out: &mut BTreeSet<String>) {
        match e {
            Expr::Term(t) => sym(t, out),
            Expr::Bin(l, _, r) => {
                expr(l, out);
                expr(r, out);
            }
        }
    }
    let mut out = BTreeSet::new();
    let atom = |a: &Atom, out: &mut BTreeSet<String>| a.args.iter().for_each(|(_, t)| sym(t, out));
    for r in prog
        .rules
        .iter()
        .filter(|r| cone.contains(r.head.rel.as_str()))
    {
        atom(&r.head, &mut out);
        for lit in &r.body {
            match lit {
                Lit::Atom(a) => atom(a, &mut out),
                Lit::Agg { over, expr: e, .. } => {
                    over.iter().for_each(|a| atom(a, &mut out));
                    expr(e, &mut out);
                }
                Lit::Cmp(l, _, r) => {
                    expr(l, &mut out);
                    expr(r, &mut out);
                }
            }
        }
    }
    prog.forbids.iter().for_each(|f| atom(&f.atom, &mut out));
    out
}

/// `u1` read in `c1` is below the rule-defined relation `rel` read in `c2`:
/// in every canonical world of every sense, the rules derive `rel` of the head.
/// The worlds identify variables with the constants of the senses, of the
/// rules and of the `forbid` constraints; worlds that break a `forbid` are
/// skipped. Exact for monotone rules (`not_monotone`); otherwise only a check.
/// Returns a world where the rules do not derive it, if there is one.
fn below_rules(
    prog: &Program,
    u1: &[Cq],
    c1: &Plane,
    rel: &str,
    c2: &Plane,
) -> Result<Option<String>, String> {
    let name = |e: &E| match e {
        E::B(i) => Term::Sym(format!("_w{i}").into()),
        E::C(c) => Term::Sym(c.into()),
    };
    let extra = rule_consts(prog, &cone(prog, rel));
    for q in u1 {
        let mut consts = q.consts();
        consts.extend(extra.iter().cloned());
        for w in worlds(q, &consts, true)? {
            let mut p = Program {
                axes: prog.axes.clone(),
                planes: prog.planes.clone(),
                rules: prog.rules.clone(),
                defeats: prog.defeats.clone(),
                status_rank: prog.status_rank.clone(),
                ..Program::default()
            };
            for (i, (r, args)) in w.atoms.iter().enumerate() {
                p.facts.push(Fact {
                    id: format!("w{i}").into(),
                    atom: Atom::new(
                        r.into(),
                        args.iter()
                            .map(|(role, e)| (role.into(), name(e)))
                            .collect(),
                        false,
                    ),
                    plane: c1.clone(),
                    status: "given".into(),
                    line: 0,
                });
            }
            p.forbids = prog.forbids.clone();
            let out = eval::evaluate(&p, c2);
            // A world the integrity constraints forbid is not a world.
            if out
                .conflicts
                .values()
                .any(|c| c.kind == eval::ConflictKind::Violation)
            {
                continue;
            }
            let goal = Atom::new(
                rel.into(),
                w.head
                    .iter()
                    .map(|(role, e)| (role.into(), name(e)))
                    .collect(),
                false,
            )
            .key();
            if !out.db.contains_key(&goal) || out.conflicts.contains_key(&goal) {
                return Ok(Some(w.to_string()));
            }
        }
    }
    Ok(None)
}

impl World {
    fn term(&self, e: &E) -> Term {
        match e {
            E::C(c) => Term::Sym(c.into()),
            E::B(i) => Term::Sym(format!("_w{i}").into()),
        }
    }

    fn facts(&self) -> (Vec<Atom>, Vec<(String, Term)>) {
        let atoms = self
            .atoms
            .iter()
            .map(|(rel, args)| {
                let args = args.iter().map(|(r, e)| (r.into(), self.term(e))).collect();
                Atom::new(rel.into(), args, false)
            })
            .collect();
        let head = self
            .head
            .iter()
            .map(|(r, e)| (r.clone(), self.term(e)))
            .collect();
        (atoms, head)
    }
}

/// Facts where concept `a` read in `pa` holds of the head and `b` read in `pb`
/// does not: a counterexample to `a ⊑ b`, if there is one.
pub type Witness = (Vec<Atom>, Vec<(String, Term)>);

pub fn witness(
    prog: &Program,
    a: &str,
    pa: &Plane,
    b: &str,
    pb: &Plane,
) -> Result<Option<Witness>, String> {
    let (ua, ub) = (normal_form(prog, a, pa)?, normal_form(prog, b, pb)?);
    witness_of(prog, &ua, pa, &ub, pb)
}

/// `witness` for concepts already in normal form, so that comparing many
/// pairs computes each normal form once.
pub fn witness_of(
    prog: &Program,
    ua: &[Cq],
    pa: &Plane,
    ub: &[Cq],
    pb: &Plane,
) -> Result<Option<Witness>, String> {
    Ok(union_counterexample(prog, ua, pa, ub, pb)?.map(|w| w.facts()))
}

pub struct Compared {
    pub relation: Relation,
    pub explanation: String,
}

fn show(name: &str, plane: &Plane, u: &[Cq]) -> String {
    let senses: Vec<String> = u.iter().map(|q| format!("  {q}\n")).collect();
    format!(
        "{name} @ {} unfolds to:\n{}",
        plane_to_string(plane),
        senses.concat()
    )
}

pub fn compare(prog: &Program, cmp: &Compare) -> Result<Compared, String> {
    let ((a, pa), (b, pb)) = (&cmp.left, &cmp.right);
    if !is_concept(prog, a) {
        return Err(format!("`{a}` is not a concept"));
    }
    let ua = normal_form(prog, a, pa)?;
    if is_concept(prog, b) {
        let ub = normal_form(prog, b, pb)?;
        let not_below = union_counterexample(prog, &ua, pa, &ub, pb)?;
        let not_above = union_counterexample(prog, &ub, pb, &ua, pa)?;
        let relation = match (&not_below, &not_above) {
            (None, None) => Relation::Same,
            (None, Some(_)) => Relation::Below,
            (Some(_), None) => Relation::Above,
            (Some(_), Some(_)) => Relation::Apart,
        };
        let mut why = String::new();
        if let Some(w) = &not_below {
            why.push_str(&format!("{a} but not {b}: {w}\n"));
        }
        if let Some(w) = &not_above {
            why.push_str(&format!("{b} but not {a}: {w}\n"));
        }
        return Ok(Compared {
            relation,
            explanation: format!("{}{}{why}", show(a, pa, &ua), show(b, pb, &ub)),
        });
    }
    if !prog.rules.iter().any(|r| r.head.rel == *b && !r.head.neg) {
        return Err(format!("`{b}` is neither a concept nor derived by a rule"));
    }
    let world = below_rules(prog, &ua, pa, b, pb)?;
    let loose = not_monotone(prog, &cone(prog, b));
    let relation = match (&world, &loose) {
        (Some(_), _) => Relation::NotBelow,
        (None, None) => Relation::Below,
        (None, Some(_)) => Relation::Unknown,
    };
    let why = match (world, loose) {
        (Some(w), _) => format!("the rules do not derive `{b}` in: {w}\n"),
        (None, Some(l)) => format!(
            "the rules derive `{b}` in every canonical world, but {l}: \
             a larger world may lose it, so this is not a proof\n"
        ),
        (None, None) => String::new(),
    };
    Ok(Compared {
        relation,
        explanation: format!(
            "{}checked against the rules for `{b}` @ {}\n{why}",
            show(a, pa, &ua),
            plane_to_string(pb)
        ),
    })
}

/// The planes a concept report covers: the named ones, and the root when some
/// concept is defined there.
fn report_planes(prog: &Program) -> Vec<(String, Plane)> {
    let mut out: Vec<(String, Plane)> = prog
        .planes
        .iter()
        .map(|(n, p)| (n.clone(), p.clone()))
        .collect();
    if prog.concepts.iter().any(|c| c.plane.is_empty()) {
        out.insert(0, ("root".into(), Plane::new()));
    }
    out
}

/// What the definitions say in each plane: unfolding level by level, the order
/// of concepts, synonyms, unions, common genera and gaps in the languages.
pub fn report(prog: &Program) -> String {
    let mut out = String::new();
    let names: BTreeSet<&str> = prog.concepts.iter().map(|c| c.head.rel.as_str()).collect();
    let langs: BTreeSet<&str> = prog.words.iter().map(|w| w.lang.as_str()).collect();
    let words_of = |c: &str| -> Vec<String> {
        let mut ws: Vec<String> = prog
            .words
            .iter()
            .filter(|w| w.concept == c)
            .map(|w| format!("{} {}", w.lang, w.word))
            .collect();
        ws.sort();
        ws
    };
    let mut shown: Vec<(String, Vec<String>)> = Vec::new();
    for (pname, plane) in report_planes(prog) {
        let visible: Vec<&str> = names
            .iter()
            .copied()
            .filter(|n| !senses(prog, n, &plane).is_empty())
            .collect();
        if visible.is_empty() {
            continue;
        }
        out.push_str(&format!("== plane {pname} {}\n", plane_to_string(&plane)));
        // The definitions visible here; a plane that sees the same ones as a
        // plane already shown says nothing new.
        let defs: Vec<String> = visible
            .iter()
            .flat_map(|n| senses(prog, n, &plane))
            .map(sense_key)
            .collect();
        if let Some((same, _)) = shown.iter().find(|(_, d)| *d == defs) {
            out.push_str(&format!("same definitions as plane {same}\n\n"));
            continue;
        }
        shown.push((pname.clone(), defs));
        let mut forms: BTreeMap<&str, Vec<Cq>> = BTreeMap::new();
        out.push_str("\ndecomposition\n");
        for &n in &visible {
            let ws = words_of(n);
            let label = if ws.is_empty() {
                String::new()
            } else {
                format!(" [{}]", ws.join(", "))
            };
            out.push_str(&format!("{n}{label}\n"));
            let mut last = String::new();
            for depth in 0.. {
                match unfold(prog, n, &plane, depth) {
                    Ok(u) => {
                        let text = senses_text(&u);
                        if text == last {
                            break;
                        }
                        out.push_str(&format!("  {}: {text}\n", depth + 1));
                        last = text;
                    }
                    Err(e) => {
                        out.push_str(&format!("  error: {e}\n"));
                        break;
                    }
                }
            }
            match normal_form(prog, n, &plane) {
                Ok(u) => {
                    let text = senses_text(&u);
                    if text != last {
                        out.push_str(&format!("  core: {text}\n"));
                    }
                    forms.insert(n, u);
                }
                Err(e) => out.push_str(&format!("  error: {e}\n")),
            }
        }
        let names: Vec<&str> = forms.keys().copied().collect();
        let mut le: BTreeSet<(&str, &str)> = BTreeSet::new();
        for &a in &names {
            for &b in &names {
                if a != b && union_contained(prog, &forms[a], &plane, &forms[b], &plane) == Ok(true)
                {
                    le.insert((a, b));
                }
            }
        }
        let same = |a: &str, b: &str| le.contains(&(a, b)) && le.contains(&(b, a));
        let below = |a: &str, b: &str| le.contains(&(a, b)) && !le.contains(&(b, a));

        out.push_str("\nsame by definition\n");
        let mut classes: Vec<Vec<&str>> = Vec::new();
        for &n in &names {
            match classes.iter_mut().find(|c| same(c[0], n)) {
                Some(c) => c.push(n),
                None => classes.push(vec![n]),
            }
        }
        for c in classes.iter().filter(|c| c.len() > 1) {
            out.push_str(&format!("  {}\n", c.join(" = ")));
        }

        out.push_str("\ndirect special cases\n");
        for &b in &names {
            let mut direct: Vec<&str> = names
                .iter()
                .copied()
                .filter(|&a| below(a, b) && !names.iter().any(|&m| below(a, m) && below(m, b)))
                .collect();
            direct.dedup();
            if !direct.is_empty() {
                out.push_str(&format!("  {b} > {}\n", direct.join(", ")));
            }
        }

        out.push_str("\nunions\n");
        for &c in &names {
            let subs: Vec<&str> = names.iter().copied().filter(|&a| below(a, c)).collect();
            for (i, &a) in subs.iter().enumerate() {
                for &b in &subs[i + 1..] {
                    if le.contains(&(a, b)) || le.contains(&(b, a)) {
                        continue;
                    }
                    let mut ab = forms[a].clone();
                    ab.extend(forms[b].iter().cloned());
                    if union_contained(prog, &forms[c], &plane, &ab, &plane) == Ok(true) {
                        out.push_str(&format!("  {c} = {a} ∪ {b}\n"));
                    }
                }
            }
        }

        out.push_str("\ncommon genus\n");
        let mut unnamed: BTreeMap<String, Vec<String>> = BTreeMap::new();
        // Pairs that are direct special cases of one concept: the genus is
        // asked of neighbours, not of every pair.
        let direct =
            |a: &str, b: &str| below(a, b) && !names.iter().any(|&m| below(a, m) && below(m, b));
        for (i, &a) in names.iter().enumerate() {
            for &b in &names[i + 1..] {
                let ([qa], [qb]) = (forms[a].as_slice(), forms[b].as_slice()) else {
                    continue;
                };
                if le.contains(&(a, b)) || le.contains(&(b, a)) {
                    continue;
                }
                if !names.iter().any(|&p| direct(a, p) && direct(b, p)) {
                    continue;
                }
                let Ok(Some(g)) = common(prog, qa, qb, &plane) else {
                    continue;
                };
                let g = vec![g];
                let named: Vec<&str> = names
                    .iter()
                    .copied()
                    .filter(|&n| {
                        union_contained(prog, &g, &plane, &forms[n], &plane) == Ok(true)
                            && union_contained(prog, &forms[n], &plane, &g, &plane) == Ok(true)
                    })
                    .collect();
                if named.is_empty() {
                    unnamed
                        .entry(g[0].to_string())
                        .or_default()
                        .push(format!("{a}+{b}"));
                } else {
                    out.push_str(&format!("  {a}, {b} -> {}\n", named.join(" = ")));
                }
            }
        }
        for (g, pairs) in &unnamed {
            out.push_str(&format!("  unnamed: {g}  <- {}\n", pairs.join(", ")));
        }

        out.push_str("\ngaps in languages\n");
        for c in &classes {
            let words: Vec<String> = c.iter().flat_map(|n| words_of(n)).collect();
            if words.is_empty() {
                continue;
            }
            for &l in &langs {
                if !words.iter().any(|w| w.split(' ').next() == Some(l)) {
                    out.push_str(&format!(
                        "  {l}: no word for {} ({})\n",
                        c.join(" = "),
                        words.join(", ")
                    ));
                }
            }
        }
        out.push('\n');
    }
    out
}

fn senses_text(u: &[Cq]) -> String {
    let parts: Vec<String> = u.iter().map(Cq::to_string).collect();
    parts.join("  |  ")
}

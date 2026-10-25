//! Normal forms: laws as rules of simplification (`docs/impl/atlas.md` §11).
//!
//! A law is turned into a rule "greater → smaller" by an order on terms
//! (Knuth–Bendix: more symbols is greater; on a tie, the first difference
//! decides, x < y < z). A law that cannot be turned so (x·y = y·x) is used
//! only where the result is smaller (ordered rewriting). Every element is
//! simplified at once to the representative of its class, its normal form.
//! Completion: where two rules overlap and give different results, the
//! difference is a new law, until the overlaps meet. Completion need not
//! end; past its limits the result is marked unfinished, and what the rules
//! decide is still true, only perhaps not all.

use crate::atlas::Term;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Var(u8),
    Con(u8),
    Op(u32, u32),
}

/// Variables of laws are below this; a second law in an overlap is shifted
/// above it.
const SHIFT: u8 = 32;
/// Constants standing for variables in the test of joinability.
const FRESH: u8 = 64;

#[derive(Default)]
struct Terms {
    nodes: Vec<Node>,
    index: BTreeMap<Node, u32>,
    size: Vec<u32>,
}

impl Terms {
    fn mk(&mut self, n: Node) -> u32 {
        if let Some(&i) = self.index.get(&n) {
            return i;
        }
        let i = self.nodes.len() as u32;
        let s = match n {
            Node::Op(a, b) => 1 + self.size[a as usize] + self.size[b as usize],
            _ => 1,
        };
        self.nodes.push(n);
        self.size.push(s);
        self.index.insert(n, i);
        i
    }

    fn op(&mut self, a: u32, b: u32) -> u32 {
        self.mk(Node::Op(a, b))
    }

    fn node(&self, t: u32) -> Node {
        self.nodes[t as usize]
    }

    fn intern(&mut self, t: &Term, constants: bool) -> u32 {
        match t {
            Term::Var(v) if constants => self.mk(Node::Con(*v)),
            Term::Var(v) => self.mk(Node::Var(*v)),
            Term::Op(a, b) => {
                let (a, b) = (self.intern(a, constants), self.intern(b, constants));
                self.op(a, b)
            }
        }
    }

    fn vars(&self, t: u32, out: &mut [u32; 128]) {
        match self.node(t) {
            Node::Var(v) => out[v as usize] += 1,
            Node::Con(_) => {}
            Node::Op(a, b) => {
                self.vars(a, out);
                self.vars(b, out);
            }
        }
    }

    /// Knuth–Bendix order, every symbol of weight 1: whether s > t.
    fn greater(&self, s: u32, t: u32) -> bool {
        if s == t {
            return false;
        }
        let (mut vs, mut vt) = ([0; 128], [0; 128]);
        self.vars(s, &mut vs);
        self.vars(t, &mut vt);
        if (0..128).any(|v| vs[v] < vt[v]) {
            return false;
        }
        let (ws, wt) = (self.size[s as usize], self.size[t as usize]);
        if ws != wt {
            return ws > wt;
        }
        match (self.node(s), self.node(t)) {
            (Node::Con(a), Node::Con(b)) => a > b,
            (Node::Op(s1, s2), Node::Op(t1, t2)) => {
                if s1 == t1 {
                    self.greater(s2, t2)
                } else {
                    self.greater(s1, t1)
                }
            }
            _ => false,
        }
    }

    fn matches(&self, pat: u32, t: u32, sub: &mut [Option<u32>]) -> bool {
        match (self.node(pat), self.node(t)) {
            (Node::Var(v), _) => match sub[v as usize] {
                Some(b) => b == t,
                None => {
                    sub[v as usize] = Some(t);
                    true
                }
            },
            (Node::Op(p1, p2), Node::Op(t1, t2)) => {
                self.matches(p1, t1, sub) && self.matches(p2, t2, sub)
            }
            _ => pat == t,
        }
    }

    /// The term with every bound variable replaced, through chains of
    /// bindings if `chain` (a unifier); none if `strict` and a variable is
    /// unbound. A match binds variables to terms that may hold variables
    /// of the same names, so it is applied in one step.
    fn subst(&mut self, t: u32, sub: &[Option<u32>], strict: bool, chain: bool) -> Option<u32> {
        match self.node(t) {
            Node::Var(v) => match sub[v as usize] {
                Some(b) if chain && b != t => self.subst(b, sub, strict, chain),
                Some(b) => Some(b),
                None if strict => None,
                None => Some(t),
            },
            Node::Con(_) => Some(t),
            Node::Op(a, b) => {
                let a = self.subst(a, sub, strict, chain)?;
                let b = self.subst(b, sub, strict, chain)?;
                Some(self.op(a, b))
            }
        }
    }

    fn walk(&self, mut t: u32, sub: &[Option<u32>]) -> u32 {
        while let Node::Var(v) = self.node(t) {
            match sub[v as usize] {
                Some(b) => t = b,
                None => break,
            }
        }
        t
    }

    fn occurs(&self, v: u8, t: u32, sub: &[Option<u32>]) -> bool {
        match self.node(self.walk(t, sub)) {
            Node::Var(w) => w == v,
            Node::Con(_) => false,
            Node::Op(a, b) => self.occurs(v, a, sub) || self.occurs(v, b, sub),
        }
    }

    fn unify(&self, a: u32, b: u32, sub: &mut [Option<u32>]) -> bool {
        let (a, b) = (self.walk(a, sub), self.walk(b, sub));
        if a == b {
            return true;
        }
        match (self.node(a), self.node(b)) {
            (Node::Var(v), _) => {
                if self.occurs(v, b, sub) {
                    return false;
                }
                sub[v as usize] = Some(b);
                true
            }
            (_, Node::Var(_)) => self.unify(b, a, sub),
            (Node::Op(a1, a2), Node::Op(b1, b2)) => {
                self.unify(a1, b1, sub) && self.unify(a2, b2, sub)
            }
            _ => false,
        }
    }

    fn shift(&mut self, t: u32) -> u32 {
        match self.node(t) {
            Node::Var(v) => self.mk(Node::Var(v + SHIFT)),
            Node::Con(_) => t,
            Node::Op(a, b) => {
                let (a, b) = (self.shift(a), self.shift(b));
                self.op(a, b)
            }
        }
    }

    /// Non-variable places of `t`, as paths (false: left part).
    fn places(&self, t: u32, path: &mut Vec<bool>, out: &mut Vec<(Vec<bool>, u32)>) {
        match self.node(t) {
            Node::Var(_) => {}
            Node::Con(_) => out.push((path.clone(), t)),
            Node::Op(a, b) => {
                out.push((path.clone(), t));
                path.push(false);
                self.places(a, path, out);
                path.pop();
                path.push(true);
                self.places(b, path, out);
                path.pop();
            }
        }
    }

    fn replace(&mut self, t: u32, path: &[bool], new: u32) -> u32 {
        let Some((&first, rest)) = path.split_first() else {
            return new;
        };
        let Node::Op(a, b) = self.node(t) else {
            unreachable!()
        };
        if first {
            let b = self.replace(b, rest, new);
            self.op(a, b)
        } else {
            let a = self.replace(a, rest, new);
            self.op(a, b)
        }
    }

    /// Preorder code: a key not depending on when the term was made.
    fn code(&self, t: u32, out: &mut Vec<u8>) {
        match self.node(t) {
            Node::Var(v) => out.push(v),
            Node::Con(c) => out.push(128 + c),
            Node::Op(a, b) => {
                out.push(255);
                self.code(a, out);
                self.code(b, out);
            }
        }
    }

    /// Variables renamed 0, 1, … in order of first occurrence in l, then r.
    fn rename(&mut self, l: u32, r: u32) -> (u32, u32) {
        fn order(ts: &Terms, t: u32, seen: &mut Vec<u8>) {
            match ts.node(t) {
                Node::Var(v) if !seen.contains(&v) => seen.push(v),
                Node::Op(a, b) => {
                    order(ts, a, seen);
                    order(ts, b, seen);
                }
                _ => {}
            }
        }
        let mut seen = Vec::new();
        order(self, l, &mut seen);
        order(self, r, &mut seen);
        let mut sub = vec![None; 128];
        for (i, &v) in seen.iter().enumerate() {
            sub[v as usize] = Some(self.mk(Node::Var(i as u8)));
        }
        // Renaming in one pass: no chains, since targets are not re-read.
        let l = self.rename_with(l, &sub);
        let r = self.rename_with(r, &sub);
        (l, r)
    }

    fn rename_with(&mut self, t: u32, sub: &[Option<u32>]) -> u32 {
        match self.node(t) {
            Node::Var(v) => sub[v as usize].unwrap(),
            Node::Con(_) => t,
            Node::Op(a, b) => {
                let (a, b) = (self.rename_with(a, sub), self.rename_with(b, sub));
                self.op(a, b)
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Law {
    l: u32,
    r: u32,
    /// Always l > r; otherwise used either way where the result is smaller.
    oriented: bool,
}

/// What completion ended with.
pub struct Theory {
    terms: Terms,
    pub laws: Vec<Law>,
    /// Whether every overlap met within the limits.
    pub finished: bool,
    memo: BTreeMap<u32, u32>,
}

/// Limits of completion: the most laws kept, and the most symbols on a
/// side of a law.
pub const MAX_LAWS: usize = 200;
pub const MAX_SIZE: u32 = 15;

impl Theory {
    /// Completion of `axioms`, each a pair of terms read for all values.
    pub fn complete(axioms: &[(Term, Term)]) -> Theory {
        let mut th = Theory {
            terms: Terms::default(),
            laws: Vec::new(),
            finished: true,
            memo: BTreeMap::new(),
        };
        // Pairs waiting, smallest first, keyed by code: the order of the
        // axioms does not matter.
        let mut queue: BTreeMap<(u32, Vec<u8>), (u32, u32)> = BTreeMap::new();
        for (l, r) in axioms {
            let l = th.terms.intern(l, false);
            let r = th.terms.intern(r, false);
            th.push(&mut queue, l, r);
        }
        while let Some((_, (l, r))) = queue.pop_first() {
            let l = th.normal(l);
            let r = th.normal(r);
            if l == r || th.joinable(l, r) {
                continue;
            }
            if th.laws.len() >= MAX_LAWS {
                th.finished = false;
                break;
            }
            let law = if th.terms.greater(l, r) {
                Law {
                    l,
                    r,
                    oriented: true,
                }
            } else if th.terms.greater(r, l) {
                Law {
                    l: r,
                    r: l,
                    oriented: true,
                }
            } else {
                Law {
                    l,
                    r,
                    oriented: false,
                }
            };
            // Laws the new one simplifies go back to the queue.
            let old = std::mem::take(&mut th.laws);
            th.laws.push(law);
            th.memo.clear();
            let mut kept = Vec::new();
            for o in old {
                let (nl, nr) = (th.normal(o.l), th.normal(o.r));
                if nl != o.l || nr != o.r {
                    th.push(&mut queue, o.l, o.r);
                } else {
                    kept.push(o);
                }
            }
            kept.push(law);
            th.laws = kept;
            th.memo.clear();
            for other in th.laws.clone() {
                for (a, b) in [(law, other), (other, law)] {
                    for (l, r) in th.overlaps(a, b) {
                        th.push(&mut queue, l, r);
                    }
                }
            }
        }
        th.memo.clear();
        th
    }

    fn push(&mut self, queue: &mut BTreeMap<(u32, Vec<u8>), (u32, u32)>, l: u32, r: u32) {
        let mut best: Option<(Vec<u8>, (u32, u32))> = None;
        for (a, b) in [(l, r), (r, l)] {
            let (a, b) = self.terms.rename(a, b);
            let mut c = Vec::new();
            self.terms.code(a, &mut c);
            c.push(254);
            self.terms.code(b, &mut c);
            if best.as_ref().is_none_or(|(bc, _)| c < *bc) {
                best = Some((c, (a, b)));
            }
        }
        let (c, (a, b)) = best.unwrap();
        let s = self.terms.size[a as usize].max(self.terms.size[b as usize]);
        if s > MAX_SIZE {
            self.finished = false;
            return;
        }
        queue.insert((s, c), (a, b));
    }

    /// The ways a law may be read left to right.
    fn sides(law: Law) -> Vec<(u32, u32)> {
        if law.oriented {
            vec![(law.l, law.r)]
        } else {
            vec![(law.l, law.r), (law.r, law.l)]
        }
    }

    /// Critical pairs: the left side of `b` unified with a non-variable
    /// place in the left side of `a`.
    fn overlaps(&mut self, a: Law, b: Law) -> Vec<(u32, u32)> {
        let mut out = Vec::new();
        for (l1, r1) in Theory::sides(a) {
            for (l2, r2) in Theory::sides(b) {
                let (l2, r2) = (self.terms.shift(l2), self.terms.shift(r2));
                let mut places = Vec::new();
                self.terms.places(l1, &mut Vec::new(), &mut places);
                for (path, at) in places {
                    let mut sub = vec![None; 128];
                    if !self.terms.unify(at, l2, &mut sub) {
                        continue;
                    }
                    let big = self.terms.replace(l1, &path, r2);
                    let p = self.terms.subst(big, &sub, false, true).unwrap();
                    let q = self.terms.subst(r1, &sub, false, true).unwrap();
                    if p != q {
                        out.push((p, q));
                    }
                }
            }
        }
        out
    }

    /// Simplest form of `t` by the laws, innermost first.
    fn normal(&mut self, t: u32) -> u32 {
        if let Some(&n) = self.memo.get(&t) {
            return n;
        }
        let u = match self.terms.node(t) {
            Node::Op(a, b) => {
                let (a, b) = (self.normal(a), self.normal(b));
                self.terms.op(a, b)
            }
            _ => t,
        };
        let mut n = u;
        'laws: for i in 0..self.laws.len() {
            let law = self.laws[i];
            for (l, r) in Theory::sides(law) {
                let mut sub = vec![None; 128];
                if !self.terms.matches(l, u, &mut sub) {
                    continue;
                }
                let Some(v) = self.terms.subst(r, &sub, true, false) else {
                    continue;
                };
                if law.oriented || self.terms.greater(u, v) {
                    n = self.normal(v);
                    break 'laws;
                }
            }
        }
        self.memo.insert(t, n);
        n
    }

    /// Whether l and r meet under every order of their variables: each
    /// order, ties included, puts fresh constants in place of them.
    fn joinable(&mut self, l: u32, r: u32) -> bool {
        let mut count = [0; 128];
        self.terms.vars(l, &mut count);
        self.terms.vars(r, &mut count);
        let vs: Vec<u8> = (0..128u8).filter(|&v| count[v as usize] > 0).collect();
        if vs.is_empty() || vs.len() > 5 {
            return false;
        }
        let mut ok = true;
        for rank in ordered_partitions(vs.len()) {
            let mut sub = vec![None; 128];
            for (k, &v) in vs.iter().enumerate() {
                sub[v as usize] = Some(self.terms.mk(Node::Con(FRESH + rank[k])));
            }
            let a = self.terms.subst(l, &sub, true, false).unwrap();
            let b = self.terms.subst(r, &sub, true, false).unwrap();
            if self.normal(a) != self.normal(b) {
                ok = false;
                break;
            }
        }
        ok
    }

    /// The normal form of a term whose variables are read as constants
    /// (the generators of a free entity).
    pub fn ground(&mut self, t: &Term) -> u32 {
        let t = self.terms.intern(t, true);
        self.normal(t)
    }

    /// How many distinct normal forms of ground terms were made so far.
    pub fn built(&self) -> usize {
        self.memo
            .values()
            .filter(|&&n| self.ground_term(n))
            .collect::<BTreeSet<_>>()
            .len()
    }

    fn ground_term(&self, t: u32) -> bool {
        match self.terms.node(t) {
            Node::Var(_) => false,
            Node::Con(c) => c < FRESH,
            Node::Op(a, b) => self.ground_term(a) && self.ground_term(b),
        }
    }

    /// The laws, each as text: "→" oriented, "~" used where smaller.
    pub fn show(&self) -> Vec<String> {
        self.laws
            .iter()
            .map(|l| {
                let s = if l.oriented { "→" } else { "~" };
                format!("{} {s} {}", self.text(l.l), self.text(l.r))
            })
            .collect()
    }

    fn text(&self, t: u32) -> String {
        match self.terms.node(t) {
            Node::Var(v) => ["x", "y", "z", "u", "v", "w"]
                .get(v as usize)
                .map(|s| s.to_string())
                .unwrap_or(format!("v{v}")),
            Node::Con(c) => format!("c{c}"),
            Node::Op(a, b) => format!("({}·{})", self.text(a), self.text(b)),
        }
    }
}

/// Every order of k things with ties, as the rank of each.
fn ordered_partitions(k: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    // Ranks are dense: the ranks used are 0..m for some m.
    let mut rank = vec![0u8; k];
    loop {
        let m = rank.iter().copied().max().map_or(0, |m| m + 1);
        if (0..m).all(|r| rank.contains(&r)) {
            out.push(rank.clone());
        }
        let mut i = 0;
        loop {
            if i == k {
                return out;
            }
            rank[i] += 1;
            if (rank[i] as usize) < k {
                break;
            }
            rank[i] = 0;
            i += 1;
        }
    }
}

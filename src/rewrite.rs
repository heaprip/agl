//! Normal forms: laws as rules of simplification (`docs/impl/atlas.md` §11).
//!
//! A law is turned into a rule "greater → smaller" by an order on terms
//! (Knuth–Bendix: more symbols is greater; on a tie, the higher action,
//! then the first difference decides, x < y < z). A law that cannot be
//! turned so (x·y = y·x) is used only where the result is smaller (ordered
//! rewriting). Every element is simplified at once to the representative
//! of its class, its normal form. Completion: where two rules overlap and
//! give different results, the difference is a new law, until the overlaps
//! meet. Completion need not end; past its limits the result is marked
//! unfinished, and what the rules decide is still true, only perhaps not
//! all.
//!
//! Actions are numbered: 0 is the operation of the entity, others come
//! from laws with "exists" (§12); each takes one or two parts.

use crate::atlas::Term;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Var(u8),
    Con(u8),
    /// An action and its parts; the second is `NIL` for one part.
    App(u8, u32, u32),
}

const NIL: u32 = u32::MAX;

/// Variables of laws are below this; a second law in an overlap is shifted
/// above it.
const SHIFT: u8 = 32;
/// Constants standing for variables in the test of joinability.
const FRESH: u8 = 64;

/// A term given from outside: variables, constants (generators below 16,
/// constants of laws with "exists" from 16) and actions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Var(u8),
    Con(u8),
    App(u8, Vec<Expr>),
}

impl Expr {
    pub fn from_term(t: &Term) -> Expr {
        match t {
            Term::Var(v) => Expr::Var(*v),
            Term::Op(a, b) => Expr::App(0, vec![Expr::from_term(a), Expr::from_term(b)]),
        }
    }
}

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
            Node::App(_, a, b) => {
                1 + self.size[a as usize] + if b == NIL { 0 } else { self.size[b as usize] }
            }
            _ => 1,
        };
        self.nodes.push(n);
        self.size.push(s);
        self.index.insert(n, i);
        i
    }

    fn app(&mut self, f: u8, a: u32, b: u32) -> u32 {
        self.mk(Node::App(f, a, b))
    }

    fn node(&self, t: u32) -> Node {
        self.nodes[t as usize]
    }

    /// The parts of a term: none, one or two.
    fn parts(&self, t: u32) -> Vec<u32> {
        match self.node(t) {
            Node::App(_, a, NIL) => vec![a],
            Node::App(_, a, b) => vec![a, b],
            _ => vec![],
        }
    }

    /// The same action on new parts.
    fn rebuild(&mut self, t: u32, parts: &[u32]) -> u32 {
        match self.node(t) {
            Node::App(f, _, _) => self.app(f, parts[0], parts.get(1).copied().unwrap_or(NIL)),
            _ => t,
        }
    }

    fn intern(&mut self, e: &Expr, constants: bool) -> u32 {
        match e {
            Expr::Var(v) if constants => self.mk(Node::Con(*v)),
            Expr::Var(v) => self.mk(Node::Var(*v)),
            Expr::Con(c) => self.mk(Node::Con(*c)),
            Expr::App(f, ps) => {
                let a = self.intern(&ps[0], constants);
                let b = match ps.get(1) {
                    Some(p) => self.intern(p, constants),
                    None => NIL,
                };
                self.app(*f, a, b)
            }
        }
    }

    fn vars(&self, t: u32, out: &mut [u32; 128]) {
        match self.node(t) {
            Node::Var(v) => out[v as usize] += 1,
            Node::Con(_) => {}
            Node::App(..) => {
                for p in self.parts(t) {
                    self.vars(p, out);
                }
            }
        }
    }

    /// Knuth–Bendix order, every symbol of weight 1, actions above
    /// constants and by number: whether s > t.
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
            (Node::App(..), Node::Con(_)) => true,
            (Node::App(f, ..), Node::App(g, ..)) if f != g => f > g,
            (Node::App(..), Node::App(..)) => {
                let (ps, pt) = (self.parts(s), self.parts(t));
                match ps.iter().zip(&pt).find(|(a, b)| a != b) {
                    Some((&a, &b)) => self.greater(a, b),
                    None => false,
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
            (Node::App(f, _, pb), Node::App(g, _, tb)) if f == g && (pb == NIL) == (tb == NIL) => {
                let (pp, tp) = (self.parts(pat), self.parts(t));
                pp.iter().zip(&tp).all(|(&p, &q)| self.matches(p, q, sub))
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
            Node::App(..) => {
                let mut ps = Vec::new();
                for p in self.parts(t) {
                    ps.push(self.subst(p, sub, strict, chain)?);
                }
                Some(self.rebuild(t, &ps))
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
        let t = self.walk(t, sub);
        match self.node(t) {
            Node::Var(w) => w == v,
            Node::Con(_) => false,
            Node::App(..) => self.parts(t).iter().any(|&p| self.occurs(v, p, sub)),
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
            (Node::App(f, _, ab), Node::App(g, _, bb)) if f == g && (ab == NIL) == (bb == NIL) => {
                let (pa, pb) = (self.parts(a), self.parts(b));
                pa.iter().zip(&pb).all(|(&p, &q)| self.unify(p, q, sub))
            }
            _ => false,
        }
    }

    fn shift(&mut self, t: u32) -> u32 {
        match self.node(t) {
            Node::Var(v) => self.mk(Node::Var(v + SHIFT)),
            Node::Con(_) => t,
            Node::App(..) => {
                let ps: Vec<u32> = self.parts(t).into_iter().map(|p| self.shift(p)).collect();
                self.rebuild(t, &ps)
            }
        }
    }

    /// Non-variable places of `t`, as paths of part numbers.
    fn places(&self, t: u32, path: &mut Vec<usize>, out: &mut Vec<(Vec<usize>, u32)>) {
        if let Node::Var(_) = self.node(t) {
            return;
        }
        out.push((path.clone(), t));
        for (k, p) in self.parts(t).into_iter().enumerate() {
            path.push(k);
            self.places(p, path, out);
            path.pop();
        }
    }

    fn replace(&mut self, t: u32, path: &[usize], new: u32) -> u32 {
        let Some((&k, rest)) = path.split_first() else {
            return new;
        };
        let mut ps = self.parts(t);
        ps[k] = self.replace(ps[k], rest, new);
        self.rebuild(t, &ps)
    }

    /// Preorder code: a key not depending on when the term was made.
    fn code(&self, t: u32, out: &mut Vec<u8>) {
        match self.node(t) {
            Node::Var(v) => out.push(v),
            Node::Con(c) => out.push(128 + c),
            Node::App(f, _, b) => {
                out.extend([255, f, (b != NIL) as u8]);
                for p in self.parts(t) {
                    self.code(p, out);
                }
            }
        }
    }

    /// Variables renamed 0, 1, … in order of first occurrence in l, then r.
    fn rename(&mut self, l: u32, r: u32) -> (u32, u32) {
        fn order(ts: &Terms, t: u32, seen: &mut Vec<u8>) {
            match ts.node(t) {
                Node::Var(v) if !seen.contains(&v) => seen.push(v),
                Node::App(..) => {
                    for p in ts.parts(t) {
                        order(ts, p, seen);
                    }
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
        let l = self.subst(l, &sub, true, false).unwrap();
        let r = self.subst(r, &sub, true, false).unwrap();
        (l, r)
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
/// The most terms kept, about 64 bytes each: past it completion stops
/// unfinished and the search for witnesses with what it has.
pub const MAX_TERMS: usize = 1 << 22;

impl Theory {
    /// Completion of `axioms`, each a pair of terms read for all values.
    pub fn complete(axioms: &[(Term, Term)]) -> Theory {
        let axioms: Vec<(Expr, Expr)> = axioms
            .iter()
            .map(|(l, r)| (Expr::from_term(l), Expr::from_term(r)))
            .collect();
        Theory::complete_exprs(&axioms)
    }

    pub fn complete_exprs(axioms: &[(Expr, Expr)]) -> Theory {
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
        // Laws ever added, by code: a law whose instances stay unjoined
        // would otherwise come back again and again.
        let mut added: BTreeSet<Vec<u8>> = BTreeSet::new();
        while let Some((_, (l, r))) = queue.pop_first() {
            let l = th.normal(l);
            let r = th.normal(r);
            if l == r || th.joinable(l, r) {
                continue;
            }
            let (l, r) = th.canonical(l, r);
            let mut c = Vec::new();
            th.terms.code(l, &mut c);
            c.push(254);
            th.terms.code(r, &mut c);
            if !added.insert(c) {
                continue;
            }
            if th.laws.len() >= MAX_LAWS || th.full() {
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

    /// The pair with variables renamed and sides in the order of least
    /// code.
    fn canonical(&mut self, l: u32, r: u32) -> (u32, u32) {
        self.keyed(l, r).1
    }

    fn keyed(&mut self, l: u32, r: u32) -> (Vec<u8>, (u32, u32)) {
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
        best.unwrap()
    }

    fn push(&mut self, queue: &mut BTreeMap<(u32, Vec<u8>), (u32, u32)>, l: u32, r: u32) {
        let (c, (a, b)) = self.keyed(l, r);
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
    pub fn normal(&mut self, t: u32) -> u32 {
        if let Some(&n) = self.memo.get(&t) {
            return n;
        }
        let u = match self.terms.node(t) {
            Node::App(..) => {
                let ps: Vec<u32> = self
                    .terms
                    .parts(t)
                    .into_iter()
                    .map(|p| self.normal(p))
                    .collect();
                self.terms.rebuild(t, &ps)
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
        for rank in ordered_partitions(vs.len()) {
            let mut sub = vec![None; 128];
            for (k, &v) in vs.iter().enumerate() {
                sub[v as usize] = Some(self.terms.mk(Node::Con(FRESH + rank[k])));
            }
            let a = self.terms.subst(l, &sub, true, false).unwrap();
            let b = self.terms.subst(r, &sub, true, false).unwrap();
            if self.normal(a) != self.normal(b) {
                return false;
            }
        }
        true
    }

    /// The normal form of a term whose variables are read as constants
    /// (the generators of a free entity).
    pub fn ground(&mut self, t: &Term) -> u32 {
        self.ground_expr(&Expr::from_term(t))
    }

    pub fn ground_expr(&mut self, e: &Expr) -> u32 {
        let t = self.terms.intern(e, true);
        self.normal(t)
    }

    /// A constant, and an action on terms already made.
    pub fn con(&mut self, c: u8) -> u32 {
        self.terms.mk(Node::Con(c))
    }

    pub fn app(&mut self, f: u8, parts: &[u32]) -> u32 {
        self.terms
            .app(f, parts[0], parts.get(1).copied().unwrap_or(NIL))
    }

    /// Whether the terms kept have reached `MAX_TERMS`.
    pub fn full(&self) -> bool {
        self.terms.nodes.len() >= MAX_TERMS
    }

    /// The number of symbols in a term.
    pub fn size(&self, t: u32) -> u32 {
        self.terms.size[t as usize]
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
            Node::App(..) => self.terms.parts(t).iter().all(|&p| self.ground_term(p)),
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

    /// A term as text: variables x, y, z, …; generators a, b, c, …;
    /// constants of laws with "exists" e16, …; actions f1, ….
    pub fn text(&self, t: u32) -> String {
        match self.terms.node(t) {
            Node::Var(v) => ["x", "y", "z", "u", "v", "w"]
                .get(v as usize)
                .map(|s| s.to_string())
                .unwrap_or(format!("v{v}")),
            Node::Con(c) if c < 16 => ((b'a' + c) as char).to_string(),
            Node::Con(c) => format!("e{c}"),
            Node::App(0, a, b) => format!("({}·{})", self.text(a), self.text(b)),
            Node::App(f, a, NIL) => format!("f{f}({})", self.text(a)),
            Node::App(f, a, b) => format!("f{f}({}, {})", self.text(a), self.text(b)),
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

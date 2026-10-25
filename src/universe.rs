//! One universe of finite relations (H75, `docs/impl/relations.md` §6).
//!
//! From one point by one rule: a token is the point, or a pair of a finite
//! set of tokens and a token (the graph model of Plotkin, Engeler and
//! Scott). An element of the universe is a set of tokens; tokens are kept
//! up to a size, so the infinite is held by finite pieces. Two relations
//! come from the building, none is chosen: E(c, t), c is in the set of t
//! (membership), and P(t, b), t leads to b. Everything else is a formula
//! over them with conjunction, "there is" and complement: applying X to Y
//! gives the b led to by a token of X whose set lies in Y; abstraction
//! turns an expression into the set of tokens whose set, put in for the
//! variable, makes the expression hold of where they lead. A formula is
//! asked of one token at a time, from the goal: a variable bound by "there
//! is" takes its values from an atom that fixes it, not from every token.

use std::collections::BTreeMap;

pub struct Universe {
    /// The set of each token, sorted; empty for the point.
    pub set: Vec<Vec<u32>>,
    /// Where each token leads; none for the point.
    pub to: Vec<Option<u32>>,
    pub size: Vec<u32>,
    /// Tokens leading to each token, and tokens whose set holds each.
    led: Vec<Vec<u32>>,
    holding: Vec<Vec<u32>>,
}

impl Universe {
    /// Every token of size at most `max`, by size, then by parts.
    pub fn new(max: u32) -> Universe {
        let mut u = Universe {
            set: vec![vec![]],
            to: vec![None],
            size: vec![1],
            led: vec![],
            holding: vec![],
        };
        for s in 2..=max {
            let made = u.set.len() as u32;
            let mut new: Vec<(Vec<u32>, u32)> = Vec::new();
            for b in 0..made {
                let budget = s - 1 - u.size[b as usize];
                let mut set = Vec::new();
                u.sets(0, made, budget, &mut set, &mut |set| {
                    new.push((set.to_vec(), b))
                });
            }
            new.retain(|(set, b)| {
                1 + u.size[*b as usize] + set.iter().map(|&c| u.size[c as usize]).sum::<u32>() == s
            });
            new.sort();
            for (set, b) in new {
                u.set.push(set);
                u.to.push(Some(b));
                u.size.push(s);
            }
        }
        let n = u.set.len();
        u.led = vec![vec![]; n];
        u.holding = vec![vec![]; n];
        for t in 0..n {
            if let Some(b) = u.to[t] {
                u.led[b as usize].push(t as u32);
            }
            for &c in &u.set[t] {
                u.holding[c as usize].push(t as u32);
            }
        }
        u
    }

    /// Sets of distinct tokens below `made`, from `from` on, of total size
    /// at most `budget`.
    fn sets(
        &self,
        from: u32,
        made: u32,
        budget: u32,
        cur: &mut Vec<u32>,
        f: &mut impl FnMut(&[u32]),
    ) {
        f(cur);
        for c in from..made {
            let sc = self.size[c as usize];
            if sc <= budget {
                cur.push(c);
                self.sets(c + 1, made, budget - sc, cur, f);
                cur.pop();
            }
        }
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn is_empty(&self) -> bool {
        self.set.is_empty()
    }
}

/// A formula over E and P; variables are small numbers.
#[derive(Clone, Debug)]
pub enum F {
    E(u8, u8),
    P(u8, u8),
    And(Vec<F>),
    Not(Box<F>),
    Exists(u8, Box<F>),
}

/// A λ-term with variables by the number of binders between them and their
/// own (de Bruijn).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum L {
    Var(usize),
    App(Box<L>, Box<L>),
    Lam(Box<L>),
}

impl L {
    pub fn app(a: L, b: L) -> L {
        L::App(Box::new(a), Box::new(b))
    }

    pub fn lam(a: L) -> L {
        L::Lam(Box::new(a))
    }

    pub fn size(&self) -> usize {
        match self {
            L::Var(_) => 1,
            L::App(a, b) => 1 + a.size() + b.size(),
            L::Lam(a) => 1 + a.size(),
        }
    }

    /// `self` with variable `k` replaced by `by` (closed terms only are put
    /// in, so nothing in `by` needs shifting).
    pub fn put(&self, k: usize, by: &L) -> L {
        match self {
            L::Var(i) if *i == k => by.clone(),
            L::Var(i) if *i > k => L::Var(i - 1),
            L::Var(i) => L::Var(*i),
            L::App(a, b) => L::app(a.put(k, by), b.put(k, by)),
            L::Lam(a) => L::lam(a.put(k + 1, by)),
        }
    }

    /// Every closed term of exactly `size` symbols, under `depth` binders.
    pub fn all(size: usize, depth: usize) -> Vec<L> {
        let mut out = Vec::new();
        if size == 1 {
            out.extend((0..depth).map(L::Var));
        }
        if size >= 2 {
            out.extend(L::all(size - 1, depth + 1).into_iter().map(L::lam));
        }
        for left in 1..size.saturating_sub(1) {
            for a in L::all(left, depth) {
                for b in L::all(size - 1 - left, depth) {
                    out.push(L::app(a.clone(), b));
                }
            }
        }
        out
    }

    /// The formula of membership in the term's element, of variable `out`:
    /// a variable is the set of its binder's token; application and
    /// abstraction as in the module text.
    pub fn formula(&self, out: u8, binders: &mut Vec<u8>, next: &mut u8) -> F {
        let mut fresh = || {
            *next += 1;
            *next - 1
        };
        match self {
            L::Var(i) => F::E(out, binders[binders.len() - 1 - i]),
            L::App(m, n) => {
                let (t, c) = (fresh(), fresh());
                let fm = m.formula(t, binders, next);
                let fnn = n.formula(c, binders, next);
                F::Exists(
                    t,
                    Box::new(F::And(vec![
                        F::P(t, out),
                        fm,
                        F::Not(Box::new(F::Exists(
                            c,
                            Box::new(F::And(vec![F::E(c, t), F::Not(Box::new(fnn))])),
                        ))),
                    ])),
                )
            }
            L::Lam(m) => {
                let b = fresh();
                binders.push(out);
                let fm = m.formula(b, binders, next);
                binders.pop();
                F::Exists(b, Box::new(F::And(vec![F::P(out, b), fm])))
            }
        }
    }
}

impl std::fmt::Display for L {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            L::Var(i) => write!(f, "{i}"),
            L::App(a, b) => write!(f, "({a} {b})"),
            L::Lam(a) => write!(f, "λ{a}"),
        }
    }
}

/// The most steps one question may take before it is left undecided.
pub const MAX_STEPS: u64 = 50_000_000;
/// The most answers remembered, about 100 bytes each, for all askers
/// together; past it an asker forgets (answers only save work, they never
/// change one).
pub const MAX_MEMO: usize = 1 << 21;

/// A subformula used inside another: its node, and for each of its
/// variables the variable of the user it stands for.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Child {
    id: usize,
    args: Vec<u8>,
}

/// A node with its variables numbered 0, 1, … in order of first use; the
/// variable bound by "there is" comes after the free ones. Equal nodes are
/// stored once, so what is learned of a subformula in one formula serves
/// every other that has it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    /// E(0, 1), or E(0, 0) when both places are one variable.
    E(bool),
    P(bool),
    And(Vec<Child>),
    Not(Child),
    Exists(Child),
}

/// Asks formulas of tokens, remembering answers by node and the values of
/// its variables.
pub struct Ask<'u> {
    u: &'u Universe,
    nodes: Vec<(Kind, u8)>,
    index: BTreeMap<Kind, usize>,
    memo: BTreeMap<(usize, Vec<u32>), bool>,
    cap: usize,
    pub steps: u64,
    /// The most steps one question may take; `MAX_STEPS` unless lowered.
    pub limit: u64,
    pub gave_up: bool,
}

impl<'u> Ask<'u> {
    pub fn new(u: &'u Universe) -> Ask<'u> {
        Ask::sharing(u, 1)
    }

    /// An asker that is one of `askers` at work together: the memory for
    /// answers is shared out between them.
    pub fn sharing(u: &'u Universe, askers: usize) -> Ask<'u> {
        Ask {
            u,
            nodes: Vec::new(),
            index: BTreeMap::new(),
            memo: BTreeMap::new(),
            cap: MAX_MEMO / askers.max(1),
            steps: 0,
            limit: MAX_STEPS,
            gave_up: false,
        }
    }

    fn intern(&mut self, kind: Kind, arity: u8) -> usize {
        if let Some(&i) = self.index.get(&kind) {
            return i;
        }
        self.nodes.push((kind.clone(), arity));
        self.index.insert(kind, self.nodes.len() - 1);
        self.nodes.len() - 1
    }

    /// Stores a formula; its node and its free variables in the node's
    /// order.
    pub fn add(&mut self, f: &F) -> (usize, Vec<u8>) {
        match f {
            F::E(a, b) | F::P(a, b) => {
                let same = a == b;
                let kind = match f {
                    F::E(..) => Kind::E(same),
                    _ => Kind::P(same),
                };
                let free = if same { vec![*a] } else { vec![*a, *b] };
                (self.intern(kind, free.len() as u8), free)
            }
            F::And(gs) => {
                let mut free: Vec<u8> = Vec::new();
                let mut kids = Vec::new();
                for g in gs {
                    let (id, gf) = self.add(g);
                    let args = gf
                        .iter()
                        .map(|v| match free.iter().position(|w| w == v) {
                            Some(p) => p as u8,
                            None => {
                                free.push(*v);
                                (free.len() - 1) as u8
                            }
                        })
                        .collect();
                    kids.push(Child { id, args });
                }
                (self.intern(Kind::And(kids), free.len() as u8), free)
            }
            F::Not(g) => {
                let (id, gf) = self.add(g);
                let args = (0..gf.len() as u8).collect();
                let n = gf.len() as u8;
                (self.intern(Kind::Not(Child { id, args }), n), gf)
            }
            F::Exists(v, g) => {
                let (id, gf) = self.add(g);
                let free: Vec<u8> = gf.iter().copied().filter(|w| w != v).collect();
                let bound = free.len() as u8;
                let args = gf
                    .iter()
                    .map(|w| {
                        if w == v {
                            bound
                        } else {
                            free.iter().position(|x| x == w).unwrap() as u8
                        }
                    })
                    .collect();
                let n = free.len() as u8;
                (self.intern(Kind::Exists(Child { id, args }), n), free)
            }
        }
    }

    /// Whether node `k` holds with its variables at `vals`; false once the
    /// steps run out (then `gave_up` is set and no answer counts).
    pub fn holds(&mut self, k: usize, vals: &[u32]) -> bool {
        if self.gave_up {
            return false;
        }
        self.steps += 1;
        if self.steps > self.limit {
            self.gave_up = true;
            return false;
        }
        if let Some(&b) = self.memo.get(&(k, vals.to_vec())) {
            return b;
        }
        let u = self.u;
        let kind = self.nodes[k].0.clone();
        let r = match kind {
            Kind::E(same) => {
                let (c, t) = (vals[0], if same { vals[0] } else { vals[1] });
                u.set[t as usize].binary_search(&c).is_ok()
            }
            Kind::P(same) => {
                let (t, b) = (vals[0], if same { vals[0] } else { vals[1] });
                u.to[t as usize] == Some(b)
            }
            Kind::And(kids) => kids.iter().all(|c| {
                let v: Vec<u32> = c.args.iter().map(|&a| vals[a as usize]).collect();
                self.holds(c.id, &v)
            }),
            Kind::Not(c) => {
                let v: Vec<u32> = c.args.iter().map(|&a| vals[a as usize]).collect();
                !self.holds(c.id, &v)
            }
            Kind::Exists(c) => {
                let bound = vals.len() as u8;
                let mut ext = vals.to_vec();
                ext.push(0);
                let mut found = false;
                for t in self.candidates(&c, bound, vals) {
                    ext[bound as usize] = t;
                    let v: Vec<u32> = c.args.iter().map(|&a| ext[a as usize]).collect();
                    if self.holds(c.id, &v) {
                        found = true;
                        break;
                    }
                }
                found
            }
        };
        if !self.gave_up {
            if self.memo.len() >= self.cap {
                self.memo.clear();
            }
            self.memo.insert((k, vals.to_vec()), r);
        }
        r
    }

    /// Values for the variable `bound` of the body `c` from the atom of the
    /// body that fixes it with the fewest values, given `vals`; every token
    /// if none does.
    fn candidates(&self, c: &Child, bound: u8, vals: &[u32]) -> Vec<u32> {
        let u = self.u;
        let atoms: Vec<Child> = match &self.nodes[c.id].0 {
            Kind::And(kids) => kids
                .iter()
                .map(|k| Child {
                    id: k.id,
                    args: k.args.iter().map(|&a| c.args[a as usize]).collect(),
                })
                .collect(),
            _ => vec![c.clone()],
        };
        let mut best: Option<Vec<u32>> = None;
        for a in atoms {
            let (x, y) = match self.nodes[a.id].0 {
                Kind::E(false) | Kind::P(false) => (a.args[0], a.args[1]),
                _ => continue,
            };
            let is_e = matches!(self.nodes[a.id].0, Kind::E(_));
            let val = |w: u8| vals[w as usize];
            let found: Option<Vec<u32>> = match (x == bound, y == bound, is_e) {
                (true, false, true) => Some(u.set[val(y) as usize].clone()),
                (false, true, true) => Some(u.holding[val(x) as usize].clone()),
                (true, false, false) => Some(u.led[val(y) as usize].clone()),
                (false, true, false) => Some(u.to[val(x) as usize].into_iter().collect()),
                _ => None,
            };
            if let Some(f) = found
                && best.as_ref().is_none_or(|b| f.len() < b.len())
            {
                best = Some(f);
            }
        }
        best.unwrap_or_else(|| (0..u.len() as u32).collect())
    }

    /// The tokens of size at most `m` in the element of a closed term;
    /// none if the steps ran out.
    pub fn element(&mut self, term: &L, m: u32) -> Option<Vec<u32>> {
        self.steps = 0;
        self.gave_up = false;
        let f = term.formula(0, &mut Vec::new(), &mut 1);
        let (root, free) = self.add(&f);
        debug_assert!(free == [0] || free.is_empty());
        let mut out = Vec::new();
        for t in 0..self.u.len() as u32 {
            if self.u.size[t as usize] > m {
                break;
            }
            let ok = if free.is_empty() {
                self.holds(root, &[])
            } else {
                self.holds(root, &[t])
            };
            if ok {
                out.push(t);
            }
        }
        (!self.gave_up).then_some(out)
    }
}

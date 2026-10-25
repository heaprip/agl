//! One universe of finite relations (H75, `docs/impl/relations.md` §6–8).
//!
//! From one point by one rule: a token is the point, or a pair of a finite
//! set of tokens and a token. An element of the universe is a set of
//! tokens; tokens are kept up to a size (the plane), so the infinite is
//! held by finite pieces. Two relations come from the building, none is
//! chosen: E(c, t), c is in the set of t, and P(t, b), t leads to b. An
//! expression is a formula over them with conjunction, "there is" and
//! complement; nothing else is given. `Ask` asks a formula of one token at a
//! time and is kept as the reference; `Find` answers it for a set of tokens
//! at a time, from the goal, taking a bound end from the narrowest relation
//! that fixes it.

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
    /// The distinct sets of tokens, and the number of each token's set.
    pub sets: Vec<Vec<u32>>,
    pub set_id: Vec<u32>,
    /// (set number, where it leads, token) for every token but the point,
    /// sorted: the token made of a set and a target.
    parts: Vec<(u32, u32, u32)>,
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
            sets: vec![],
            set_id: vec![],
            parts: vec![],
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
        let mut distinct: Vec<&Vec<u32>> = u.set.iter().collect();
        distinct.sort();
        distinct.dedup();
        u.sets = distinct.into_iter().cloned().collect();
        u.set_id = (0..n)
            .map(|t| u.sets.binary_search(&u.set[t]).unwrap() as u32)
            .collect();
        u.parts = (0..n)
            .filter_map(|t| u.to[t].map(|b| (u.set_id[t], b, t as u32)))
            .collect();
        u.parts.sort_unstable();
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

    /// The token of set number `s` leading to `b`, if within the limit.
    fn token(&self, s: u32, b: u32) -> Option<u32> {
        self.parts
            .binary_search_by(|&(x, y, _)| (x, y).cmp(&(s, b)))
            .ok()
            .map(|i| self.parts[i].2)
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

/// Formulas stored once, in canonical form, each with a mask of its
/// variables used only as holders of a set (second place of E): only the
/// set of such a variable matters, so answers are kept by the set.
struct Store {
    nodes: Vec<(Kind, Vec<bool>)>,
    index: BTreeMap<Kind, usize>,
}

impl Store {
    fn new() -> Store {
        Store {
            nodes: Vec::new(),
            index: BTreeMap::new(),
        }
    }

    fn intern(&mut self, kind: Kind, arity: u8) -> usize {
        if let Some(&i) = self.index.get(&kind) {
            return i;
        }
        let mut holder = vec![true; arity as usize];
        let mut through = |c: &Child, nodes: &[(Kind, Vec<bool>)], bound: Option<u8>| {
            for (j, &a) in c.args.iter().enumerate() {
                if Some(a) != bound && !nodes[c.id].1[j] {
                    holder[a as usize] = false;
                }
            }
        };
        match &kind {
            Kind::E(false) => holder[0] = false,
            Kind::E(true) | Kind::P(_) => holder.iter_mut().for_each(|h| *h = false),
            Kind::And(kids) => kids.iter().for_each(|c| through(c, &self.nodes, None)),
            Kind::Not(c) => through(c, &self.nodes, None),
            Kind::Exists(c) => through(c, &self.nodes, Some(arity)),
        }
        self.nodes.push((kind.clone(), holder));
        self.index.insert(kind, self.nodes.len() - 1);
        self.nodes.len() - 1
    }

    /// Stores a formula; its node and its free variables in the node's
    /// order.
    fn add(&mut self, f: &F) -> (usize, Vec<u8>) {
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

    /// The key of answers: holders by their set.
    fn key(&self, u: &Universe, k: usize, vals: &[u32]) -> Vec<u32> {
        vals.iter()
            .zip(&self.nodes[k].1)
            .map(|(&v, &h)| {
                if h && v != FREE {
                    u.set_id[v as usize] | 1 << 31
                } else {
                    v
                }
            })
            .collect()
    }
}

/// The tokens of size at most `m`.
fn small(u: &Universe, m: u32) -> Vec<u32> {
    (0..u.len() as u32)
        .take_while(|&t| u.size[t as usize] <= m)
        .collect()
}

/// Asks formulas of tokens one at a time, remembering answers by node and
/// the values of its variables. The reference for `Find`.
pub struct Ask<'u> {
    u: &'u Universe,
    store: Store,
    memo: BTreeMap<(usize, Vec<u32>), bool>,
    cap: usize,
    pub steps: u64,
    /// The most steps one question may take; `MAX_STEPS` unless lowered.
    pub limit: u64,
    pub gave_up: bool,
}

impl<'u> Ask<'u> {
    pub fn new(u: &'u Universe) -> Ask<'u> {
        Ask {
            u,
            store: Store::new(),
            memo: BTreeMap::new(),
            cap: MAX_MEMO,
            steps: 0,
            limit: MAX_STEPS,
            gave_up: false,
        }
    }

    /// Whether node `k` holds with its variables at `vals`; false once the
    /// steps run out (then `gave_up` is set and no answer counts).
    fn holds(&mut self, k: usize, vals: &[u32]) -> bool {
        if self.gave_up {
            return false;
        }
        self.steps += 1;
        if self.steps > self.limit {
            self.gave_up = true;
            return false;
        }
        let key = self.store.key(self.u, k, vals);
        if let Some(&b) = self.memo.get(&(k, key.clone())) {
            return b;
        }
        let u = self.u;
        let kind = self.store.nodes[k].0.clone();
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
            self.memo.insert((k, key), r);
        }
        r
    }

    /// Values for the variable `bound` of the body `c` from the atom of the
    /// body that fixes it with the fewest values, given `vals`; every token
    /// if none does.
    fn candidates(&self, c: &Child, bound: u8, vals: &[u32]) -> Vec<u32> {
        let u = self.u;
        let atoms: Vec<Child> = match &self.store.nodes[c.id].0 {
            Kind::And(kids) => kids.iter().map(|k| k.through(c)).collect(),
            _ => vec![c.clone()],
        };
        let mut best: Option<Vec<u32>> = None;
        for a in atoms {
            let (x, y) = match self.store.nodes[a.id].0 {
                Kind::E(false) | Kind::P(false) => (a.args[0], a.args[1]),
                _ => continue,
            };
            let is_e = matches!(self.store.nodes[a.id].0, Kind::E(_));
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

    /// The tokens of size at most `m` for which a formula of variable 0
    /// holds; none if the steps ran out.
    pub fn element(&mut self, f: &F, m: u32) -> Option<Vec<u32>> {
        self.steps = 0;
        self.gave_up = false;
        let (root, free) = self.store.add(f);
        let mut out = Vec::new();
        for t in small(self.u, m) {
            let vals: &[u32] = if free.is_empty() { &[] } else { &[t] };
            if self.holds(root, vals) {
                out.push(t);
            }
        }
        (!self.gave_up).then_some(out)
    }
}

impl Child {
    /// This child of a node used inside `user`: its arguments in the
    /// user's variables.
    fn through(&self, user: &Child) -> Child {
        Child {
            id: self.id,
            args: self.args.iter().map(|&a| user.args[a as usize]).collect(),
        }
    }
}

/// The most tokens one question of a finder may touch (its step is one
/// token handled, not one formula asked, so the bound is larger).
pub const MAX_TOUCHED: u64 = 1 << 31;

/// The most bytes of answers a finder keeps; past it, it forgets (answers
/// only save work, they never change one).
pub const MAX_BYTES: usize = 1 << 28;

/// The place of the variable asked for, in the values given; and "no
/// variable asked": the answer is then [0] for true, [] for false.
const FREE: u32 = u32::MAX;
const NONE: u8 = u8::MAX;

/// Answers a formula for a set of tokens at a time, only on the tokens
/// asked for: which of `want` make it hold, the other variables fixed. A
/// bound variable takes its values from the narrowest of: a relation to a
/// fixed end, a relation to the variable asked for, or a set it must lie
/// within (its set inside a small fixed set: the subsets of that set, by
/// Codd's division). What is learned is kept per node and fixed ends (by
/// their set where only the set matters): the tokens asked and those found.
pub struct Find<'u> {
    u: &'u Universe,
    store: Store,
    memo: BTreeMap<(usize, Vec<u32>), (Vec<u32>, Vec<u32>)>,
    bytes: usize,
    cap: usize,
    pub steps: u64,
    /// The most tokens one question may touch; `MAX_TOUCHED` unless lowered.
    pub limit: u64,
    pub gave_up: bool,
}

/// A part of the body of "there is" and what it mentions.
struct Part {
    c: Child,
    bound: bool,
    out: bool,
}

impl<'u> Find<'u> {
    pub fn new(u: &'u Universe) -> Find<'u> {
        Find::sharing(u, 1)
    }

    /// A finder that is one of `finders` kept at once: `MAX_BYTES` is shared
    /// out between them.
    pub fn sharing(u: &'u Universe, finders: usize) -> Find<'u> {
        Find {
            u,
            store: Store::new(),
            memo: BTreeMap::new(),
            bytes: 0,
            cap: MAX_BYTES / finders.max(1),
            steps: 0,
            limit: MAX_TOUCHED,
            gave_up: false,
        }
    }

    /// The values of `want` for variable `out` of node `k` (or, with `out`
    /// NONE, [0] if it holds) that make it hold, the others at `vals`.
    fn find(&mut self, k: usize, vals: &[u32], out: u8, want: &[u32]) -> Vec<u32> {
        if self.gave_up || want.is_empty() {
            return Vec::new();
        }
        let mut fixed = vals.to_vec();
        if out != NONE {
            fixed[out as usize] = FREE;
        }
        let key = (k, self.store.key(self.u, k, &fixed));
        let (rest, have) = match self.memo.get(&key) {
            Some((asked, found)) => (minus(want, asked), within(want, found)),
            None => (want.to_vec(), Vec::new()),
        };
        if rest.is_empty() {
            return have;
        }
        let new = self.compute(k, &fixed, out, &rest);
        if self.gave_up {
            return Vec::new();
        }
        if self.bytes > self.cap {
            self.memo.clear();
            self.bytes = 0;
        }
        let words = key.1.len();
        let e = self.memo.entry(key).or_default();
        // Bytes held: the three vectors' elements (kept without spare
        // room) and about 120 for the entry, its headers and its share of
        // the tree.
        let size = |e: &(Vec<u32>, Vec<u32>)| 4 * (e.0.len() + e.1.len() + words) + 120;
        let before = if e.0.is_empty() { 0 } else { size(e) };
        e.0 = union(&e.0, &rest);
        e.1 = union(&e.1, &new);
        e.0.shrink_to_fit();
        e.1.shrink_to_fit();
        self.bytes = self.bytes + size(e) - before;
        union(&have, &new)
    }

    /// Whether node `k` holds with all its variables at `vals`.
    fn holds(&mut self, k: usize, vals: &[u32]) -> bool {
        !self.find(k, vals, NONE, &[0]).is_empty()
    }

    /// A child's values and the place of `out` in them.
    fn args(c: &Child, vals: &[u32], out: u8) -> (Vec<u32>, u8) {
        let v = c.args.iter().map(|&a| vals[a as usize]).collect();
        let o = c
            .args
            .iter()
            .position(|&a| a == out)
            .map_or(NONE, |p| p as u8);
        (v, o)
    }

    fn compute(&mut self, k: usize, vals: &[u32], out: u8, want: &[u32]) -> Vec<u32> {
        let u = self.u;
        self.steps += want.len() as u64 + 1;
        if self.steps > self.limit {
            self.gave_up = true;
            return Vec::new();
        }
        let truth = |b: bool| if b { want.to_vec() } else { Vec::new() };
        if out != NONE && self.store.nodes[k].1[out as usize] {
            // Only the set of the asked variable matters: once per set.
            let mut by: Vec<(u32, u32)> = want.iter().map(|&t| (u.set_id[t as usize], t)).collect();
            by.sort_unstable();
            let mut fixed = vals.to_vec();
            let mut out_set = Vec::new();
            for group in by.chunk_by(|a, b| a.0 == b.0) {
                fixed[out as usize] = group[0].1;
                if self.holds(k, &fixed) {
                    out_set.extend(group.iter().map(|g| g.1));
                }
            }
            out_set.sort_unstable();
            return out_set;
        }
        let kind = self.store.nodes[k].0.clone();
        match kind {
            Kind::E(true) => {
                let t = |x: u32| u.set[x as usize].binary_search(&x).is_ok();
                if out == NONE {
                    truth(t(vals[0]))
                } else {
                    want.iter().copied().filter(|&x| t(x)).collect()
                }
            }
            Kind::P(true) => {
                let t = |x: u32| u.to[x as usize] == Some(x);
                if out == NONE {
                    truth(t(vals[0]))
                } else {
                    want.iter().copied().filter(|&x| t(x)).collect()
                }
            }
            Kind::E(false) => match out {
                0 => within(want, &u.set[vals[1] as usize]),
                1 => within(want, &u.holding[vals[0] as usize]),
                _ => truth(u.set[vals[1] as usize].binary_search(&vals[0]).is_ok()),
            },
            Kind::P(false) => match out {
                0 => within(want, &u.led[vals[1] as usize]),
                1 => match u.to[vals[0] as usize] {
                    Some(b) => within(want, &[b]),
                    None => Vec::new(),
                },
                _ => truth(u.to[vals[0] as usize] == Some(vals[1])),
            },
            Kind::Not(c) => {
                let (v, o) = Self::args(&c, vals, out);
                let yes = self.find(c.id, &v, o, want);
                minus(want, &yes)
            }
            Kind::And(kids) => {
                // Fixed parts first, then relations, then the rest, then
                // complements: each narrows what the next is asked of.
                let rank = |c: &Child, nodes: &[(Kind, Vec<bool>)]| {
                    let has = c.args.contains(&out);
                    match (&nodes[c.id].0, has) {
                        (_, false) => 0,
                        (Kind::E(_) | Kind::P(_), _) => 1,
                        (Kind::Not(_), _) => 3,
                        _ => 2,
                    }
                };
                let mut order: Vec<&Child> = kids.iter().collect();
                order.sort_by_key(|c| rank(c, &self.store.nodes));
                let mut w = want.to_vec();
                for c in order {
                    let (v, o) = Self::args(c, vals, out);
                    if o == NONE {
                        if !self.holds(c.id, &v) {
                            return Vec::new();
                        }
                    } else {
                        w = self.find(c.id, &v, o, &w);
                    }
                    if w.is_empty() {
                        break;
                    }
                }
                w
            }
            Kind::Exists(c) => self.exists(&c, vals, out, want),
        }
    }

    /// "There is" with body `c`, its bound variable after `vals`.
    fn exists(&mut self, c: &Child, vals: &[u32], out: u8, want: &[u32]) -> Vec<u32> {
        let u = self.u;
        let bound = vals.len() as u8;
        let mut ext = vals.to_vec();
        ext.push(FREE);
        let kids: Vec<Child> = match &self.store.nodes[c.id].0 {
            Kind::And(kids) => kids.iter().map(|k| k.through(c)).collect(),
            _ => vec![c.clone()],
        };
        let parts: Vec<Part> = kids
            .into_iter()
            .map(|c| Part {
                bound: c.args.contains(&bound),
                out: out != NONE && c.args.contains(&out),
                c,
            })
            .collect();
        // Parts of neither: fixed truth; of the asked variable only: narrow
        // the want first.
        let mut want = want.to_vec();
        for p in parts.iter().filter(|p| !p.bound) {
            let (v, o) = Self::args(&p.c, &ext, out);
            if o == NONE {
                if !self.holds(p.c.id, &v) {
                    return Vec::new();
                }
            } else {
                want = self.find(p.c.id, &v, o, &want);
            }
        }
        if want.is_empty() {
            return want;
        }
        // Where the bound variable comes from: the fewest candidates.
        let mut best: Option<Vec<u32>> = None;
        let mut take = |f: Vec<u32>| {
            if best.as_ref().is_none_or(|b| f.len() < b.len()) {
                best = Some(f);
            }
        };
        for p in &parts {
            let kind = &self.store.nodes[p.c.id].0;
            if let (Kind::E(false) | Kind::P(false), true) = (kind, p.bound) {
                let (x, y) = (p.c.args[0], p.c.args[1]);
                let is_e = matches!(kind, Kind::E(_));
                let other = if x == bound { y } else { x };
                let ends = |w: u32| -> Vec<u32> {
                    match (x == bound, is_e) {
                        (true, true) => u.set[w as usize].clone(),
                        (false, true) => u.holding[w as usize].clone(),
                        (true, false) => u.led[w as usize].clone(),
                        (false, false) => u.to[w as usize].into_iter().collect(),
                    }
                };
                if other == out {
                    let mut f: Vec<u32> = want.iter().flat_map(|&w| ends(w)).collect();
                    f.sort_unstable();
                    f.dedup();
                    take(f);
                } else {
                    take(ends(ext[other as usize]));
                }
            }
            if !p.out
                && let Some(within_set) = self.division(&p.c, bound, &ext)
            {
                // Tokens whose set is a subset of a small fixed set, leading
                // where a part says (the asked values or a fixed token).
                let targets = self.target(&parts, bound, out, &ext);
                let mut f = Vec::new();
                for s in subsets_of(&within_set) {
                    let Ok(sid) = u.sets.binary_search(&s) else {
                        continue;
                    };
                    let sid = sid as u32;
                    match targets {
                        Some(None) => f.extend(want.iter().filter_map(|&b| u.token(sid, b))),
                        Some(Some(b)) => f.extend(u.token(sid, b)),
                        None => {
                            let lo = u.parts.partition_point(|&(x, _, _)| x < sid);
                            let hi = u.parts.partition_point(|&(x, _, _)| x <= sid);
                            f.extend(u.parts[lo..hi].iter().map(|p| p.2));
                        }
                    }
                }
                f.sort_unstable();
                f.dedup();
                take(f);
            }
        }
        let mut cands = best.unwrap_or_else(|| (0..u.len() as u32).collect());
        self.steps += cands.len() as u64;
        // Parts of the bound variable only: one set-at-a-time pass each.
        for p in parts.iter().filter(|p| p.bound && !p.out) {
            let (v, o) = Self::args(&p.c, &ext, bound);
            cands = self.find(p.c.id, &v, o, &cands);
            if cands.is_empty() {
                return Vec::new();
            }
        }
        if out == NONE {
            return vec![0];
        }
        let both: Vec<&Part> = parts.iter().filter(|p| p.bound && p.out).collect();
        if both.is_empty() {
            return want;
        }
        // Parts of both: for each candidate, the asked values it reaches.
        let mut found: Vec<u32> = Vec::new();
        for t in cands {
            if self.gave_up {
                return Vec::new();
            }
            ext[bound as usize] = t;
            let mut w = minus(&want, &found);
            for p in &both {
                let (v, o) = Self::args(&p.c, &ext, out);
                w = self.find(p.c.id, &v, o, &w);
                if w.is_empty() {
                    break;
                }
            }
            found = union(&found, &w);
            if found.len() == want.len() {
                break;
            }
        }
        found
    }

    /// Where a part says the bound variable leads: to the asked variable
    /// (Some(None)), to a fixed token (Some(Some(b))), or nowhere said.
    fn target(&self, parts: &[Part], bound: u8, out: u8, ext: &[u32]) -> Option<Option<u32>> {
        let mut best = None;
        for p in parts {
            if !matches!(self.store.nodes[p.c.id].0, Kind::P(false)) || p.c.args[0] != bound {
                continue;
            }
            let w = p.c.args[1];
            if w != out && ext[w as usize] != FREE {
                return Some(Some(ext[w as usize]));
            }
            if w == out && out != NONE {
                best = Some(None);
            }
        }
        best
    }

    /// If part `c` says "every member of the bound variable's set is in
    /// the set of a fixed token" — not (there is a member c' with not
    /// E(c', fixed)) — that fixed set.
    fn division(&self, c: &Child, bound: u8, ext: &[u32]) -> Option<Vec<u32>> {
        let nodes = &self.store.nodes;
        let Kind::Not(inner) = &nodes[c.id].0 else {
            return None;
        };
        // `inner` in the user's variables; its body in its own, with the
        // member it binds after them.
        let inner = inner.through(c);
        let Kind::Exists(body) = &nodes[inner.id].0 else {
            return None;
        };
        let Kind::And(kids) = &nodes[body.id].0 else {
            return None;
        };
        if kids.len() != 2 {
            return None;
        }
        let member = inner.args.len() as u8;
        let user = |x: u8| inner.args.get(x as usize).copied();
        let mut fixed = None;
        let mut holds_member = false;
        for k in kids.iter().map(|k| k.through(body)) {
            match &nodes[k.id].0 {
                Kind::E(false) if k.args[0] == member && user(k.args[1]) == Some(bound) => {
                    holds_member = true
                }
                Kind::Not(g) => {
                    let g = g.through(&k);
                    let Kind::E(false) = nodes[g.id].0 else {
                        return None;
                    };
                    if g.args[0] != member {
                        return None;
                    }
                    let w = user(g.args[1])?;
                    if w == bound || ext[w as usize] == FREE {
                        return None;
                    }
                    fixed = Some(self.u.set[ext[w as usize] as usize].clone());
                }
                _ => return None,
            }
        }
        if holds_member { fixed } else { None }
    }

    /// The tokens of size at most `m` for which a formula of variable 0
    /// holds; none if the steps ran out.
    pub fn element(&mut self, f: &F, m: u32) -> Option<Vec<u32>> {
        self.steps = 0;
        self.gave_up = false;
        let (root, free) = self.store.add(f);
        let out = if free.is_empty() {
            if self.holds(root, &[]) {
                small(self.u, m)
            } else {
                Vec::new()
            }
        } else {
            self.find(root, &[FREE], 0, &small(self.u, m))
        };
        (!self.gave_up).then_some(out)
    }
}

/// Every subset of a sorted set, each sorted.
fn subsets_of(s: &[u32]) -> Vec<Vec<u32>> {
    (0..1u32 << s.len())
        .map(|m| {
            (0..s.len())
                .filter(|i| m >> i & 1 == 1)
                .map(|i| s[i])
                .collect()
        })
        .collect()
}

/// Sorted `a` without sorted `b`.
fn minus(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut j = 0;
    let mut out = Vec::new();
    for &x in a {
        while j < b.len() && b[j] < x {
            j += 1;
        }
        if j == b.len() || b[j] != x {
            out.push(x);
        }
    }
    out
}

/// Sorted `a` within sorted `b`; the longer one is searched, not walked.
fn within(a: &[u32], b: &[u32]) -> Vec<u32> {
    if b.len() * 8 < a.len() {
        return b
            .iter()
            .copied()
            .filter(|x| a.binary_search(x).is_ok())
            .collect();
    }
    if a.len() * 8 < b.len() {
        return a
            .iter()
            .copied()
            .filter(|x| b.binary_search(x).is_ok())
            .collect();
    }
    let mut j = 0;
    let mut out = Vec::new();
    for &x in a {
        while j < b.len() && b[j] < x {
            j += 1;
        }
        if j < b.len() && b[j] == x {
            out.push(x);
        }
    }
    out
}

/// Sorted union of sorted `a` and `b`.
fn union(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if j == b.len() || (i < a.len() && a[i] < b[j]) {
            out.push(a[i]);
            i += 1;
        } else {
            if i < a.len() && a[i] == b[j] {
                i += 1;
            }
            out.push(b[j]);
            j += 1;
        }
    }
    out
}

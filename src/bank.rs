//! A bank of relation expressions grown from data (H72, `docs/impl/clean.md`).
//!
//! An expression is a binary conjunctive query over one relation hole `R`:
//! atoms `R(u, v)` over variables and an ordered pair of heads. Expressions
//! grow by gluing two of them at their ends, the join of rule bodies being
//! the only operation; converse, composition, intersection and identity of
//! relation algebra are particular gluings. Expressions with the same extent
//! on the relation form a class, and only the first member of a class grows
//! further (observational equivalence: Escher, TRANSIT). Two members of one
//! class that logic does not equate (homomorphisms both ways, Chandra and
//! Merlin) are an equality of the world; an inclusion of extents that logic
//! does not give is an inclusion of the world. No property is named here.

use std::collections::BTreeMap;
use std::fmt;

use crate::model::{Name, Program, Term};

/// Rounds of gluing in the first stage.
pub const ROUNDS: usize = 2;
/// Largest domain the first stage takes.
pub const MAX_FIELD: usize = 16;

/// Ways to identify ends of A (positions 0, 1) with ends of B (2, 3): none,
/// one or two, never two ends of one part (gluing with identity gives that).
const MERGES: [&[(usize, usize)]; 7] = [
    &[],
    &[(0, 2)],
    &[(0, 3)],
    &[(1, 2)],
    &[(1, 3)],
    &[(0, 2), (1, 3)],
    &[(0, 3), (1, 2)],
];

/// Block of each end position under merge `m`: its smallest position.
fn blocks(m: usize) -> [usize; 4] {
    let mut b = [0, 1, 2, 3];
    for &(p, q) in MERGES[m] {
        b[q] = b[p];
    }
    b
}

/// Ordered head pairs (as positions) available under merge `m`.
fn heads(m: usize) -> Vec<(usize, usize)> {
    let b = blocks(m);
    let mut ds: Vec<usize> = b.to_vec();
    ds.sort();
    ds.dedup();
    let mut out = Vec::new();
    for &p in &ds {
        for &q in &ds {
            out.push((p, q));
        }
    }
    out
}

/// A set of pairs over a field of `n` elements, as bits.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ext {
    n: usize,
    bits: Vec<u64>,
}

impl Ext {
    pub fn empty(n: usize) -> Self {
        Ext {
            n,
            bits: vec![0; (n * n).div_ceil(64).max(1)],
        }
    }

    pub fn from_pairs(n: usize, pairs: &[(usize, usize)]) -> Self {
        let mut e = Ext::empty(n);
        pairs.iter().for_each(|&(i, j)| e.set(i, j));
        e
    }

    pub fn n(&self) -> usize {
        self.n
    }

    pub fn get(&self, i: usize, j: usize) -> bool {
        let k = i * self.n + j;
        self.bits[k / 64] >> (k % 64) & 1 == 1
    }

    pub fn set(&mut self, i: usize, j: usize) {
        let k = i * self.n + j;
        self.bits[k / 64] |= 1 << (k % 64);
    }

    pub fn subset(&self, o: &Ext) -> bool {
        self.bits.iter().zip(&o.bits).all(|(a, b)| a & !b == 0)
    }

    pub fn count(&self) -> usize {
        self.bits.iter().map(|w| w.count_ones() as usize).sum()
    }

    fn diagonal(n: usize) -> Self {
        let mut e = Ext::empty(n);
        (0..n).for_each(|i| e.set(i, i));
        e
    }
}

/// Extents of gluing `a` and `b` under merge `m`, for every head pair of
/// `heads(m)`: the pairs of head values over assignments of the end blocks
/// that put the ends of `a` in `a` and the ends of `b` in `b`.
fn glue_ext(a: &Ext, b: &Ext, m: usize) -> Vec<Ext> {
    let n = a.n;
    let bl = blocks(m);
    let mut ds: Vec<usize> = bl.to_vec();
    ds.sort();
    ds.dedup();
    let slot = |p: usize| ds.iter().position(|&d| d == bl[p]).unwrap();
    let hs = heads(m);
    let mut out = vec![Ext::empty(n); hs.len()];
    let k = ds.len();
    let mut v = vec![0usize; k];
    let pos: [usize; 4] = [slot(0), slot(1), slot(2), slot(3)];
    let hpos: Vec<(usize, usize)> = hs.iter().map(|&(p, q)| (slot(p), slot(q))).collect();
    'all: loop {
        if a.get(v[pos[0]], v[pos[1]]) && b.get(v[pos[2]], v[pos[3]]) {
            for (e, &(p, q)) in out.iter_mut().zip(&hpos) {
                e.set(v[p], v[q]);
            }
        }
        for d in (0..k).rev() {
            v[d] += 1;
            if v[d] < n {
                continue 'all;
            }
            v[d] = 0;
        }
        break;
    }
    out
}

/// A binary conjunctive query over the hole `R`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Shape {
    pub atoms: Vec<(u8, u8)>,
    pub vars: u8,
    pub head: (u8, u8),
}

impl Shape {
    pub fn rel() -> Self {
        Shape {
            atoms: vec![(0, 1)],
            vars: 2,
            head: (0, 1),
        }
    }

    pub fn id() -> Self {
        Shape {
            atoms: vec![],
            vars: 1,
            head: (0, 0),
        }
    }

    /// `a` and `b` glued under merge `m` with heads at positions `head`.
    pub fn glue(a: &Shape, b: &Shape, m: usize, head: (usize, usize)) -> Shape {
        let na = a.vars as usize;
        let total = na + b.vars as usize;
        let mut uf: Vec<usize> = (0..total).collect();
        fn find(uf: &mut [usize], x: usize) -> usize {
            let mut r = x;
            while uf[r] != r {
                r = uf[r];
            }
            uf[x] = r;
            r
        }
        let ends = [
            a.head.0 as usize,
            a.head.1 as usize,
            na + b.head.0 as usize,
            na + b.head.1 as usize,
        ];
        for &(p, q) in MERGES[m] {
            let (x, y) = (find(&mut uf, ends[p]), find(&mut uf, ends[q]));
            uf[x.max(y)] = x.min(y);
        }
        let mut atoms: Vec<(usize, usize)> = a
            .atoms
            .iter()
            .map(|&(u, v)| (u as usize, v as usize))
            .chain(
                b.atoms
                    .iter()
                    .map(|&(u, v)| (na + u as usize, na + v as usize)),
            )
            .collect();
        for at in &mut atoms {
            *at = (find(&mut uf, at.0), find(&mut uf, at.1));
        }
        let h = (find(&mut uf, ends[head.0]), find(&mut uf, ends[head.1]));
        normal(&atoms, h)
    }

    /// The extent on relation `r`, evaluated from the atoms.
    pub fn eval(&self, r: &Ext) -> Ext {
        let n = r.n();
        let mut out = Ext::empty(n);
        let mut v = vec![0usize; self.vars as usize];
        'all: loop {
            if self
                .atoms
                .iter()
                .all(|&(a, b)| r.get(v[a as usize], v[b as usize]))
            {
                out.set(v[self.head.0 as usize], v[self.head.1 as usize]);
            }
            for d in (0..v.len()).rev() {
                v[d] += 1;
                if v[d] < n {
                    continue 'all;
                }
                v[d] = 0;
            }
            break;
        }
        out
    }

    /// Whether logic gives every answer of `self` as an answer of `o`: a
    /// homomorphism from `o` to `self` fixing the heads (Chandra, Merlin).
    pub fn within(&self, o: &Shape) -> bool {
        hom(o, &self.atoms, self.head).is_some()
    }

    /// Equal by logic: contained both ways.
    pub fn same(&self, o: &Shape) -> bool {
        self.atoms.len() == o.atoms.len() && self.vars == o.vars && self.within(o) && o.within(self)
    }
}

/// The core of the query given by `atoms` and heads `h`, relabelled.
fn normal(atoms: &[(usize, usize)], h: (usize, usize)) -> Shape {
    let mut s = relabel(atoms, h);
    'shrink: loop {
        for i in 0..s.atoms.len() {
            let rest: Vec<(u8, u8)> = s
                .atoms
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, &a)| a)
                .collect();
            if let Some(map) = hom(&s, &rest, s.head) {
                let atoms: Vec<(usize, usize)> = s
                    .atoms
                    .iter()
                    .map(|&(u, v)| (map[u as usize] as usize, map[v as usize] as usize))
                    .collect();
                s = relabel(&atoms, (s.head.0 as usize, s.head.1 as usize));
                continue 'shrink;
            }
        }
        return s;
    }
}

/// Heads first, then the other variables by first appearance; atoms sorted.
fn relabel(atoms: &[(usize, usize)], h: (usize, usize)) -> Shape {
    let mut ids: BTreeMap<usize, u8> = BTreeMap::new();
    let mut next = 0u8;
    let mut id = |x: usize, ids: &mut BTreeMap<usize, u8>| {
        *ids.entry(x).or_insert_with(|| {
            next += 1;
            next - 1
        })
    };
    let head = (id(h.0, &mut ids), id(h.1, &mut ids));
    let mut out: Vec<(u8, u8)> = atoms
        .iter()
        .map(|&(u, v)| (id(u, &mut ids), id(v, &mut ids)))
        .collect();
    out.sort();
    out.dedup();
    Shape {
        atoms: out,
        vars: ids.len() as u8,
        head,
    }
}

/// A map of the variables of `p` sending its heads to `head` and each of
/// its atoms to one of `atoms`.
fn hom(p: &Shape, atoms: &[(u8, u8)], head: (u8, u8)) -> Option<Vec<u8>> {
    const FREE: u8 = u8::MAX;
    let mut map = vec![FREE; p.vars as usize];
    for (x, y) in [(p.head.0, head.0), (p.head.1, head.1)] {
        match map[x as usize] {
            FREE => map[x as usize] = y,
            z if z != y => return None,
            _ => {}
        }
    }
    fn go(i: usize, p: &[(u8, u8)], q: &[(u8, u8)], map: &mut Vec<u8>) -> bool {
        let Some(&(u, v)) = p.get(i) else {
            return true;
        };
        for &(x, y) in q {
            let (mu, mv) = (map[u as usize], map[v as usize]);
            if (mu != FREE && mu != x) || (mv != FREE && mv != y) || (u == v && x != y) {
                continue;
            }
            map[u as usize] = x;
            map[v as usize] = y;
            if go(i + 1, p, q, map) {
                return true;
            }
            map[u as usize] = mu;
            map[v as usize] = mv;
        }
        false
    }
    if !go(0, &p.atoms, atoms, &mut map) {
        return None;
    }
    for m in &mut map {
        if *m == FREE {
            *m = head.0;
        }
    }
    Some(map)
}

const VARS: &[&str] = &["x", "y", "a", "b", "c", "d", "e", "f", "g", "h"];

impl fmt::Display for Shape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // A diagonal head is one variable; the others skip the name `y`.
        let skip = usize::from(self.head.0 == self.head.1);
        let v = |i: u8| {
            let i = i as usize + if i > 0 { skip } else { 0 };
            VARS.get(i).copied().unwrap_or("?")
        };
        let (x, y) = (v(self.head.0), v(self.head.1));
        write!(f, "{{{x},{y} |")?;
        for (i, &(a, b)) in self.atoms.iter().enumerate() {
            let sep = if i == 0 { " " } else { ", " };
            write!(f, "{sep}R({},{})", v(a), v(b))?;
        }
        write!(f, "}}")
    }
}

/// How an entry was built: from the relation, identity, or gluing two
/// earlier entries of the same bank.
#[derive(Clone, Copy, Debug)]
pub enum Build {
    Rel,
    Id,
    Glue {
        a: usize,
        b: usize,
        m: u8,
        head: (u8, u8),
    },
}

#[derive(Clone, Debug)]
pub struct Entry {
    pub shape: Shape,
    pub ext: Ext,
    pub round: usize,
    pub build: Build,
}

/// The bank of one relation: entries, and classes of entries by extent; the
/// first member of a class is its representative.
#[derive(Clone, Debug)]
pub struct Bank {
    pub rel: Name,
    pub entries: Vec<Entry>,
    pub classes: Vec<Vec<usize>>,
    /// Gluings evaluated.
    pub glued: usize,
}

impl Bank {
    /// Grows the bank of a relation with extent `r` for `ROUNDS` rounds.
    /// With `prune`, only representatives grow; without, every entry does.
    pub fn grow(rel: Name, r: Ext, prune: bool) -> Bank {
        let n = r.n();
        let mut bank = Bank {
            rel,
            entries: Vec::new(),
            classes: Vec::new(),
            glued: 0,
        };
        let mut by_ext: BTreeMap<Ext, usize> = BTreeMap::new();
        let leaves = [
            (Shape::rel(), r, Build::Rel),
            (Shape::id(), Ext::diagonal(n), Build::Id),
        ];
        for (shape, ext, build) in leaves {
            bank.add(&mut by_ext, shape, ext, 0, build);
        }
        for round in 1..=ROUNDS {
            let growers: Vec<usize> = if prune {
                bank.classes.iter().map(|c| c[0]).collect()
            } else {
                (0..bank.entries.len()).collect()
            };
            for (k, &i) in growers.iter().enumerate() {
                for &j in &growers[k..] {
                    let (ei, ej) = (&bank.entries[i], &bank.entries[j]);
                    if ei.round + 1 != round && ej.round + 1 != round {
                        continue;
                    }
                    for m in 0..MERGES.len() {
                        let exts = glue_ext(&bank.entries[i].ext, &bank.entries[j].ext, m);
                        for (ext, head) in exts.into_iter().zip(heads(m)) {
                            bank.glued += 1;
                            let shape = Shape::glue(
                                &bank.entries[i].shape,
                                &bank.entries[j].shape,
                                m,
                                head,
                            );
                            let build = Build::Glue {
                                a: i,
                                b: j,
                                m: m as u8,
                                head: (head.0 as u8, head.1 as u8),
                            };
                            bank.add(&mut by_ext, shape, ext, round, build);
                        }
                    }
                }
            }
        }
        bank
    }

    fn add(
        &mut self,
        by_ext: &mut BTreeMap<Ext, usize>,
        shape: Shape,
        ext: Ext,
        round: usize,
        build: Build,
    ) {
        let class = match by_ext.get(&ext) {
            Some(&c) => {
                if self.classes[c]
                    .iter()
                    .any(|&e| self.entries[e].shape.same(&shape))
                {
                    return;
                }
                c
            }
            None => {
                by_ext.insert(ext.clone(), self.classes.len());
                self.classes.push(Vec::new());
                self.classes.len() - 1
            }
        };
        self.classes[class].push(self.entries.len());
        self.entries.push(Entry {
            shape,
            ext,
            round,
            build,
        });
    }

    pub fn class_of(&self, shape: &Shape) -> Option<usize> {
        self.classes
            .iter()
            .position(|c| c.iter().any(|&e| self.entries[e].shape.same(shape)))
    }

    pub fn ext(&self, class: usize) -> &Ext {
        &self.entries[self.classes[class][0]].ext
    }

    /// Covering inclusions between classes, with whether logic gives them.
    pub fn order(&self) -> Vec<(usize, usize, bool)> {
        let k = self.classes.len();
        let below = |c: usize, d: usize| c != d && self.ext(c).subset(self.ext(d));
        let mut out = Vec::new();
        for c in 0..k {
            for d in 0..k {
                if below(c, d) && !(0..k).any(|e| below(c, e) && below(e, d)) {
                    let logic = self.classes[c].iter().any(|&p| {
                        self.classes[d]
                            .iter()
                            .any(|&q| self.entries[p].shape.within(&self.entries[q].shape))
                    });
                    out.push((c, d, logic));
                }
            }
        }
        out
    }

    /// Classes by extent and their covering inclusions, as extents only: what
    /// pruning must not change.
    pub fn signature(&self) -> String {
        let mut order: Vec<(&Ext, &Ext)> = self
            .order()
            .into_iter()
            .map(|(c, d, _)| (self.ext(c), self.ext(d)))
            .collect();
        order.sort();
        let mut exts: Vec<&Ext> = (0..self.classes.len()).map(|c| self.ext(c)).collect();
        exts.sort();
        format!("{exts:?}\n{order:?}")
    }

    /// Extent of entry `e` rebuilt on another relation `r`.
    pub fn eval(&self, e: usize, r: &Ext, memo: &mut BTreeMap<usize, Ext>) -> Ext {
        if let Some(x) = memo.get(&e) {
            return x.clone();
        }
        let x = match self.entries[e].build {
            Build::Rel => r.clone(),
            Build::Id => Ext::diagonal(r.n),
            Build::Glue { a, b, m, head } => {
                let (ea, eb) = (self.eval(a, r, memo), self.eval(b, r, memo));
                let i = heads(m as usize)
                    .iter()
                    .position(|&h| h == (head.0 as usize, head.1 as usize))
                    .unwrap();
                glue_ext(&ea, &eb, m as usize).swap_remove(i)
            }
        };
        memo.insert(e, x.clone());
        x
    }
}

/// Binary relations of the program's root context, over one domain: every
/// symbol of a binary relation, sorted by name (one universe, as in relation
/// algebra). Name and extent of each; the domain; why nothing, if so.
pub fn relations(prog: &Program) -> (Vec<(Name, Ext)>, Vec<Name>, Option<String>) {
    let out = crate::eval::evaluate(prog, &Default::default());
    let binary: BTreeMap<&str, (&str, &str)> = prog
        .relations
        .iter()
        .filter_map(|(rel, roles)| match roles.as_slice() {
            [r0, r1] => Some((rel.as_str(), (r0.as_str(), r1.as_str()))),
            _ => None,
        })
        .collect();
    let mut pairs: BTreeMap<&str, Vec<(Name, Name)>> =
        binary.keys().map(|&r| (r, Vec::new())).collect();
    for (atom, _) in out.db.values() {
        let Some(&(r0, r1)) = binary.get(atom.rel.as_str()) else {
            continue;
        };
        let arg = |role: &str| match atom.args.iter().find(|(r, _)| r.as_str() == role) {
            Some((_, Term::Sym(s))) => Some(s.clone()),
            _ => None,
        };
        if let (false, Some(a), Some(b)) = (atom.neg, arg(r0), arg(r1)) {
            pairs.get_mut(atom.rel.as_str()).unwrap().push((a, b));
        }
    }
    let mut domain: Vec<Name> = pairs
        .values()
        .flatten()
        .flat_map(|(a, b)| [a.clone(), b.clone()])
        .collect();
    domain.sort();
    domain.dedup();
    if domain.is_empty() || domain.len() > MAX_FIELD {
        let why = format!("domain of {} elements", domain.len());
        return (Vec::new(), domain, Some(why));
    }
    let at = |s: &Name| domain.binary_search(s).unwrap();
    let rels = pairs
        .into_iter()
        .map(|(rel, list)| {
            let idx: Vec<(usize, usize)> = list.iter().map(|(a, b)| (at(a), at(b))).collect();
            (Name::from(rel), Ext::from_pairs(domain.len(), &idx))
        })
        .collect();
    (rels, domain, None)
}

/// A set of relations of the world, as exact dense bits.
pub type Objs = crate::bits::DenseSet;

/// Kinds of relations: a formal context of relations against inclusions of
/// shapes from every bank, and its concepts (H72, section 4).
pub struct Kinds {
    /// Relations of the world.
    pub n: usize,
    /// Shapes from all banks, logic-distinct: (bank, entry).
    pub vocab: Vec<(usize, usize)>,
    /// Non-logical inclusions `s ⊆ t` of vocabulary shapes holding on some
    /// relation, grouped by the set of relations where they hold: the set,
    /// and the inclusions, first one shown.
    pub attrs: Vec<(Objs, Vec<(usize, usize)>)>,
    pub concepts: Vec<Kind>,
}

#[derive(Clone, Debug)]
pub struct Kind {
    pub extent: Objs,
    /// Indices into `attrs` holding on the whole extent.
    pub content: Vec<usize>,
    /// A shortest set of content attributes that singles the extent out in
    /// this world, searched up to `MAX_L`; empty for the laws of the whole
    /// world or when longer.
    pub generators: Vec<usize>,
    /// Relations needed for a name: k·(L − 1) > L; `None` when L ≤ 1.
    pub threshold: Option<usize>,
    pub named: bool,
}

/// Longest shape in the words of kinds: the first round of gluing. Longer
/// shapes wait for anchors (H72, section 8).
pub const KIND_ATOMS: usize = 2;

/// Longest definition searched.
pub const MAX_L: usize = 3;

impl Kinds {
    pub fn build(banks: &[Bank]) -> Kinds {
        let n = banks.len();
        let mut vocab: Vec<(usize, usize)> = Vec::new();
        let mut buckets: BTreeMap<(u8, usize, bool), Vec<usize>> = BTreeMap::new();
        for (b, bank) in banks.iter().enumerate() {
            for (e, entry) in bank.entries.iter().enumerate() {
                let s = &entry.shape;
                if s.atoms.len() > KIND_ATOMS {
                    continue;
                }
                let key = (s.vars, s.atoms.len(), s.head.0 == s.head.1);
                let bucket = buckets.entry(key).or_default();
                if !bucket
                    .iter()
                    .any(|&v| banks[vocab[v].0].entries[vocab[v].1].shape.same(s))
                {
                    bucket.push(vocab.len());
                    vocab.push((b, e));
                }
            }
        }
        let shape = |v: usize| &banks[vocab[v].0].entries[vocab[v].1].shape;
        let exts: Vec<Vec<Ext>> = banks
            .iter()
            .map(|r| Kinds::eval_vocab(banks, &vocab, r.ext(0)))
            .collect();
        let mut groups: BTreeMap<Objs, Vec<(usize, usize)>> = BTreeMap::new();
        for s in 0..vocab.len() {
            for t in 0..vocab.len() {
                if s == t || shape(s).within(shape(t)) {
                    continue;
                }
                let mut objs = Objs::none(n);
                for (r, e) in exts.iter().enumerate() {
                    if e[s].subset(&e[t]) {
                        objs.insert(r);
                    }
                }
                if !objs.is_empty() {
                    groups.entry(objs).or_default().push((s, t));
                }
            }
        }
        let attrs: Vec<(Objs, Vec<(usize, usize)>)> = groups.into_iter().collect();
        // Concepts defined by one or two laws: the closures of attribute
        // extents and of their pairwise intersections. The whole lattice is
        // far larger (H72, section 8).
        let all = Objs::all(n);
        let mut extents: std::collections::BTreeSet<Objs> = std::collections::BTreeSet::new();
        for i in 0..attrs.len() {
            for j in i..attrs.len() {
                let x = attrs[i].0.and(&attrs[j].0);
                if x.count() >= 2 {
                    extents.insert(x);
                }
            }
        }
        let mut kept = Vec::new();
        for e in extents {
            if closure(&attrs, &e, &all) == e {
                kept.push(e);
            }
        }
        kept.sort_by_key(|e| (std::cmp::Reverse(e.count()), e.clone()));
        let concepts = kept
            .into_iter()
            .map(|e| Kinds::kind(&attrs, e, &all))
            .collect();
        Kinds {
            n,
            vocab,
            attrs,
            concepts,
        }
    }

    /// The kind with extent `extent`: content, shortest definition, name.
    fn kind(attrs: &[(Objs, Vec<(usize, usize)>)], extent: Objs, all: &Objs) -> Kind {
        let content: Vec<usize> = (0..attrs.len())
            .filter(|&a| extent.within(&attrs[a].0))
            .collect();
        let generators = if extent == *all {
            Vec::new()
        } else {
            cover(attrs, &content, &all.minus(&extent))
        };
        let l = generators.len();
        let threshold = (l >= 2).then(|| l / (l - 1) + 1);
        let named = threshold.is_some_and(|k| extent.count() >= k);
        Kind {
            extent,
            content,
            generators,
            threshold,
            named,
        }
    }

    /// The kind of the smallest concept holding relations `objs`.
    pub fn kind_of(&self, objs: &[usize]) -> Kind {
        let all = Objs::all(self.n);
        let mut e = Objs::none(self.n);
        objs.iter().for_each(|&o| e.insert(o));
        let e = closure(&self.attrs, &e, &all);
        Kinds::kind(&self.attrs, e, &all)
    }

    /// Extents of every vocabulary shape on relation `r`.
    pub fn eval_vocab(banks: &[Bank], vocab: &[(usize, usize)], r: &Ext) -> Vec<Ext> {
        let mut memos: Vec<BTreeMap<usize, Ext>> = vec![BTreeMap::new(); banks.len()];
        vocab
            .iter()
            .map(|&(b, e)| banks[b].eval(e, r, &mut memos[b]))
            .collect()
    }

    /// Description saved by naming a kind: k·(L − 1) − L.
    pub fn saving(k: &Kind) -> isize {
        let l = k.generators.len() as isize;
        k.extent.count() as isize * (l - 1) - l
    }
}

/// Relations holding every attribute that holds on all of `objs`.
fn closure(attrs: &[(Objs, Vec<(usize, usize)>)], objs: &Objs, all: &Objs) -> Objs {
    attrs
        .iter()
        .filter(|(o, _)| objs.within(o))
        .fold(all.clone(), |m, (o, _)| m.and(o))
}

/// A smallest set, up to `MAX_L`, of `content` attributes failing between
/// them on every relation of `outside`; the first in attribute order among
/// the smallest. Empty when none is that short.
fn cover(attrs: &[(Objs, Vec<(usize, usize)>)], content: &[usize], outside: &Objs) -> Vec<usize> {
    // Where each attribute fails outside; one attribute per such set.
    let mut by_sig: BTreeMap<Objs, usize> = BTreeMap::new();
    for &a in content {
        let sig = outside.minus(&attrs[a].0);
        if !sig.is_empty() {
            by_sig.entry(sig).or_insert(a);
        }
    }
    let sigs: Vec<(Objs, usize)> = by_sig.into_iter().collect();
    let found = |pick: &[usize]| {
        let mut out: Vec<usize> = pick.iter().map(|&i| sigs[i].1).collect();
        out.sort();
        out
    };
    let mut best: Option<Vec<usize>> = None;
    let keep = |best: &mut Option<Vec<usize>>, c: Vec<usize>| {
        if best.as_ref().is_none_or(|b| c < *b) {
            *best = Some(c);
        }
    };
    for (i, (s, _)) in sigs.iter().enumerate() {
        if s == outside {
            keep(&mut best, found(&[i]));
        }
    }
    if let Some(b) = best {
        return b;
    }
    for i in 0..sigs.len() {
        for j in i + 1..sigs.len() {
            if sigs[i].0.or(&sigs[j].0) == *outside {
                keep(&mut best, found(&[i, j]));
            }
        }
    }
    if best.is_some() || MAX_L < 3 {
        return best.unwrap_or_default();
    }
    for i in 0..sigs.len() {
        for j in i + 1..sigs.len() {
            let ij = sigs[i].0.or(&sigs[j].0);
            if ij == sigs[i].0 || ij == sigs[j].0 {
                continue;
            }
            for (k, (sk, _)) in sigs.iter().enumerate().skip(j + 1) {
                if ij.or(sk) == *outside {
                    keep(&mut best, found(&[i, j, k]));
                }
            }
        }
    }
    best.unwrap_or_default()
}

/// Banks (in full with `verbose`) and kinds of a clean world, printed.
pub fn render(banks: &[Bank], kinds: &Kinds, verbose: bool) -> String {
    let mut s = String::new();
    let glued: usize = banks.iter().map(|b| b.glued).sum();
    let classes: usize = banks.iter().map(|b| b.classes.len()).sum();
    s += &format!(
        "{} relations, {classes} classes, {glued} gluings\n",
        banks.len()
    );
    for bank in banks.iter().filter(|_| verbose) {
        s += &format!(
            "relation {} — {} classes, {} entries, {} gluings\n",
            bank.rel,
            bank.classes.len(),
            bank.entries.len(),
            bank.glued
        );
        for (c, members) in bank.classes.iter().enumerate() {
            // Equalities of the world, shortest first, the short forms
            // written out; the representative grows, the shortest is shown.
            let mut ms = members.clone();
            ms.sort_by_key(|&e| bank.entries[e].shape.atoms.len());
            let first = &bank.entries[ms[0]].shape;
            s += &format!("  c{c} [{}] {first}", bank.ext(c).count());
            let (short, long): (Vec<usize>, Vec<usize>) = ms[1..]
                .iter()
                .partition(|&&e| bank.entries[e].shape.atoms.len() <= 2);
            for e in short {
                s += &format!(" = {}", bank.entries[e].shape);
            }
            if !long.is_empty() {
                s += &format!(" (+{} longer)", long.len());
            }
            s += "\n";
        }
        let world: Vec<String> = bank
            .order()
            .into_iter()
            .filter(|&(_, _, logic)| !logic)
            .map(|(c, d, _)| format!("c{c} ⊆ c{d}"))
            .collect();
        s += &format!("  inclusions of the world: {}\n", world.join(", "));
    }
    let shape = |v: usize| &banks[kinds.vocab[v].0].entries[kinds.vocab[v].1].shape;
    let attr = |a: usize| {
        let (p, q) = kinds.attrs[a].1[0];
        let more = kinds.attrs[a].1.len() - 1;
        format!("{} ⊆ {} (+{more} alike)", shape(p), shape(q))
    };
    let named = kinds.concepts.iter().filter(|k| k.named).count();
    s += &format!(
        "kinds — {} shapes, {} attributes, {} concepts, {named} named\n",
        kinds.vocab.len(),
        kinds.attrs.len(),
        kinds.concepts.len()
    );
    // Named kinds, the largest saving first.
    let mut order: Vec<usize> = (0..kinds.concepts.len())
        .filter(|&k| kinds.concepts[k].named)
        .collect();
    order.sort_by_key(|&k| (std::cmp::Reverse(Kinds::saving(&kinds.concepts[k])), k));
    for (i, &k) in order.iter().enumerate() {
        let c = &kinds.concepts[k];
        let names: Vec<String> = c.extent.iter().map(|r| banks[r].rel.to_string()).collect();
        let shown = if names.len() > 8 {
            format!("{} … ({})", names[..8].join(", "), names.len())
        } else {
            names.join(", ")
        };
        s += &format!(
            "  kind_{}: k = {}, L = {}, saving {}, content {}: {{{shown}}}\n",
            i + 1,
            c.extent.count(),
            c.generators.len(),
            Kinds::saving(c),
            c.content.len()
        );
        if verbose || i < 10 {
            for &g in &c.generators {
                s += &format!("    {}\n", attr(g));
            }
        }
    }
    s
}

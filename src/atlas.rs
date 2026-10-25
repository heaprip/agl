//! An atlas of finite operations (H74, `docs/impl/atlas.md`).
//!
//! An entity is a table of one binary operation on n elements, up to
//! renaming of the elements. A law is a sentence of an enumerated language,
//! never a chosen one: an equation of two terms of depth two or less, for
//! all values; or an equation of terms of depth one or less under any prefix
//! of quantifiers over its variables. A microtheory is a set of laws that
//! hold together; it is closed when no law holds on all its entities without
//! being in it. Models of a set of laws are searched cell by cell, with laws
//! read in three values on a partial table and isomorphic branches cut (the
//! least number heuristic of finite model finders such as Mace4).

use crate::sat::{Lit, Solver};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// A table of a binary operation on `n` elements; `None` for a cell not
/// filled yet.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Table {
    pub n: u8,
    pub cells: Vec<Option<u8>>,
}

impl Table {
    pub fn get(&self, a: u8, b: u8) -> Option<u8> {
        self.cells[a as usize * self.n as usize + b as usize]
    }

    /// Every table on `n` elements, in order of their cells.
    pub fn all(n: u8) -> Vec<Table> {
        let cells = (n as usize).pow(2);
        let count = (n as u64).pow(cells as u32);
        (0..count)
            .map(|mut k| {
                let mut t = Table {
                    n,
                    cells: vec![None; cells],
                };
                for c in t.cells.iter_mut() {
                    *c = Some((k % n as u64) as u8);
                    k /= n as u64;
                }
                t
            })
            .collect()
    }

    /// The least relabelling of the table over all permutations of the
    /// elements: equal for isomorphic tables and only for them.
    pub fn canonical(&self) -> Table {
        let n = self.n as usize;
        let mut best: Option<Table> = None;
        let mut perm: Vec<u8> = (0..self.n).collect();
        loop {
            let mut t = Table {
                n: self.n,
                cells: vec![None; n * n],
            };
            for a in 0..n {
                for b in 0..n {
                    let v = self.cells[a * n + b].map(|v| perm[v as usize]);
                    t.cells[perm[a] as usize * n + perm[b] as usize] = v;
                }
            }
            if best.as_ref().is_none_or(|b| t < *b) {
                best = Some(t);
            }
            if !next_perm(&mut perm) {
                return best.unwrap();
            }
        }
    }
}

impl Table {
    /// The table on pairs: (a, b)·(c, d) = (a·c, b·d), the pair (a, b)
    /// numbered a·m + b for `o` of m elements.
    pub fn times(&self, o: &Table) -> Table {
        let (n, m) = (self.n as usize, o.n as usize);
        let k = n * m;
        let mut t = Table {
            n: k as u8,
            cells: vec![None; k * k],
        };
        for x in 0..k {
            for y in 0..k {
                let a = self.get((x / m) as u8, (y / m) as u8);
                let b = o.get((x % m) as u8, (y % m) as u8);
                t.cells[x * k + y] = a.zip(b).map(|(a, b)| a * m as u8 + b);
            }
        }
        t
    }
}

/// For each of `ents` (canonical tables), the ways it is the product of two
/// of them, each of at least two elements: pairs of indices, the first not
/// above the second. None: the entity does not split.
pub fn splits(ents: &[Table]) -> Vec<Vec<(usize, usize)>> {
    let mut out = vec![Vec::new(); ents.len()];
    let max = ents.iter().map(|t| t.n as usize).max().unwrap_or(0);
    for i in 0..ents.len() {
        for j in i..ents.len() {
            let (a, b) = (ents[i].n as usize, ents[j].n as usize);
            if a < 2 || b < 2 || a * b > max {
                continue;
            }
            let p = ents[i].times(&ents[j]).canonical();
            if let Some(k) = ents.iter().position(|e| *e == p) {
                out[k].push((i, j));
            }
        }
    }
    out
}

/// Every way to write entity `i` as a product of entities that do not
/// split, as sorted lists of indices, each way once.
pub fn factorizations(splits: &[Vec<(usize, usize)>], i: usize) -> Vec<Vec<usize>> {
    if splits[i].is_empty() {
        return vec![vec![i]];
    }
    let mut out = BTreeSet::new();
    for &(a, b) in &splits[i] {
        for fa in factorizations(splits, a) {
            for fb in factorizations(splits, b) {
                let mut f: Vec<usize> = fa.iter().chain(&fb).copied().collect();
                f.sort();
                out.insert(f);
            }
        }
    }
    out.into_iter().collect()
}

fn next_perm(p: &mut [u8]) -> bool {
    let Some(i) = (1..p.len()).rev().find(|&i| p[i - 1] < p[i]) else {
        return false;
    };
    let j = (i..p.len()).rev().find(|&j| p[j] > p[i - 1]).unwrap();
    p.swap(i - 1, j);
    p[i..].reverse();
    true
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.n as usize;
        let rows: Vec<String> = (0..n)
            .map(|a| {
                (0..n)
                    .map(|b| self.cells[a * n + b].map_or("?".into(), |v| v.to_string()))
                    .collect::<Vec<_>>()
                    .join("")
            })
            .collect();
        write!(f, "{}", rows.join("/"))
    }
}

/// A term over variables 0, 1, 2 (x, y, z).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Var(u8),
    Op(Box<Term>, Box<Term>),
}

impl Term {
    fn depth(&self) -> usize {
        match self {
            Term::Var(_) => 0,
            Term::Op(a, b) => 1 + a.depth().max(b.depth()),
        }
    }

    fn vars(&self, out: &mut Vec<u8>) {
        match self {
            Term::Var(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Term::Op(a, b) => {
                a.vars(out);
                b.vars(out);
            }
        }
    }

    /// The value of the term, or the set of values it may still take: an
    /// empty cell takes one of its `dom` values, a term over an unknown
    /// argument any value.
    fn eval(&self, t: &Table, dom: &[u16], env: &[u8; 3]) -> Result<u8, u16> {
        match self {
            Term::Var(v) => Ok(env[*v as usize]),
            Term::Op(a, b) => match (a.eval(t, dom, env), b.eval(t, dom, env)) {
                (Ok(a), Ok(b)) => {
                    let c = a as usize * t.n as usize + b as usize;
                    t.cells[c].ok_or(dom[c])
                }
                _ => Err(u16::MAX),
            },
        }
    }

    /// Every term up to `depth` over three variables, shallow first.
    pub fn up_to(depth: usize) -> Vec<Term> {
        let mut terms: Vec<Term> = (0..3).map(Term::Var).collect();
        for _ in 0..depth {
            let prev = terms.clone();
            for a in &prev {
                for b in &prev {
                    let t = Term::Op(Box::new(a.clone()), Box::new(b.clone()));
                    if !terms.contains(&t) {
                        terms.push(t);
                    }
                }
            }
        }
        terms
    }

    fn rename(&self, map: &[u8; 3]) -> Term {
        match self {
            Term::Var(v) => Term::Var(map[*v as usize]),
            Term::Op(a, b) => Term::Op(Box::new(a.rename(map)), Box::new(b.rename(map))),
        }
    }
}

const VAR: [&str; 3] = ["x", "y", "z"];

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{}", VAR[*v as usize]),
            Term::Op(a, b) => {
                let side = |t: &Term| match t {
                    Term::Var(_) => t.to_string(),
                    _ => format!("({t})"),
                };
                write!(f, "{}·{}", side(a), side(b))
            }
        }
    }
}

/// A law: an equation under a prefix of quantifiers over its variables;
/// `true` in the prefix is "for all", `false` is "there is".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Law {
    pub prefix: Vec<(u8, bool)>,
    pub left: Term,
    pub right: Term,
}

impl fmt::Display for Law {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for &(v, all) in &self.prefix {
            write!(f, "{}{}", if all { "∀" } else { "∃" }, VAR[v as usize])?;
        }
        write!(f, ": {} = {}", self.left, self.right)
    }
}

impl Law {
    /// The law in three values on a possibly partial table: `Some(true)`
    /// holds whatever the empty cells, `Some(false)` fails whatever they
    /// are, `None` not yet known.
    pub fn holds(&self, t: &Table) -> Option<bool> {
        self.holds_in(t, &vec![u16::MAX; t.cells.len()])
    }

    /// The same, with an empty cell known to take one of its `dom` values.
    pub fn holds_in(&self, t: &Table, dom: &[u16]) -> Option<bool> {
        let mut env = [0u8; 3];
        self.go(t, dom, 0, &mut env)
    }

    fn go(&self, t: &Table, dom: &[u16], i: usize, env: &mut [u8; 3]) -> Option<bool> {
        let Some(&(v, all)) = self.prefix.get(i) else {
            let bit = |v: u8| 1u16 << v;
            return match (self.left.eval(t, dom, env), self.right.eval(t, dom, env)) {
                (Ok(l), Ok(r)) => Some(l == r),
                (Ok(v), Err(s)) | (Err(s), Ok(v)) => (s & bit(v) == 0).then_some(false),
                (Err(a), Err(b)) => (a & b == 0).then_some(false),
            };
        };
        let mut unknown = false;
        for x in 0..t.n {
            env[v as usize] = x;
            match self.go(t, dom, i + 1, env) {
                Some(b) if b != all => return Some(b),
                None => unknown = true,
                _ => {}
            }
        }
        if unknown { None } else { Some(all) }
    }

    /// The least form of the law over renamings of its variables and the
    /// two sides; neighbouring quantifiers of one kind commute, so each run
    /// of them is sorted.
    fn normal(&self) -> Law {
        let mut perm = [0u8, 1, 2];
        let mut best: Option<Law> = None;
        loop {
            let mut prefix: Vec<(u8, bool)> = self
                .prefix
                .iter()
                .map(|&(v, a)| (perm[v as usize], a))
                .collect();
            let mut i = 0;
            while i < prefix.len() {
                let j = (i..prefix.len())
                    .find(|&j| prefix[j].1 != prefix[i].1)
                    .unwrap_or(prefix.len());
                prefix[i..j].sort();
                i = j;
            }
            let (l, r) = (self.left.rename(&perm), self.right.rename(&perm));
            for (left, right) in [(l.clone(), r.clone()), (r, l)] {
                let c = Law {
                    prefix: prefix.clone(),
                    left,
                    right,
                };
                if best.as_ref().is_none_or(|b| c < *b) {
                    best = Some(c);
                }
            }
            if !next_perm(&mut perm) {
                return best.unwrap();
            }
        }
    }
}

/// The language: every equation of distinct terms up to depth 2 for all
/// values, and every equation of distinct terms up to depth 1 under every
/// prefix of quantifiers over its variables, in every order. Laws equal up
/// to renaming of variables, swapping sides or commuting quantifiers of one
/// kind are kept once.
pub fn language() -> Vec<Law> {
    let mut out: BTreeSet<Law> = BTreeSet::new();
    let deep = Term::up_to(2);
    let shallow: Vec<Term> = deep.iter().filter(|t| t.depth() <= 1).cloned().collect();
    let mut add = |l: Term, r: Term, prefixes: Vec<Vec<(u8, bool)>>| {
        for prefix in prefixes {
            let law = Law {
                prefix,
                left: l.clone(),
                right: r.clone(),
            };
            out.insert(law.normal());
        }
    };
    for (i, l) in deep.iter().enumerate() {
        for r in &deep[i + 1..] {
            let mut vs = Vec::new();
            l.vars(&mut vs);
            r.vars(&mut vs);
            vs.sort();
            let all: Vec<(u8, bool)> = vs.iter().map(|&v| (v, true)).collect();
            add(l.clone(), r.clone(), vec![all]);
        }
    }
    for (i, l) in shallow.iter().enumerate() {
        for r in &shallow[i + 1..] {
            let mut vs = Vec::new();
            l.vars(&mut vs);
            r.vars(&mut vs);
            vs.sort();
            let mut prefixes = Vec::new();
            let mut order = vs.clone();
            loop {
                for mask in 0..1u32 << order.len() {
                    prefixes.push(
                        order
                            .iter()
                            .enumerate()
                            .map(|(k, &v)| (v, mask >> k & 1 == 0))
                            .collect(),
                    );
                }
                if !next_perm(&mut order) {
                    break;
                }
            }
            add(l.clone(), r.clone(), prefixes);
        }
    }
    out.into_iter().collect()
}

/// Entities of sizes 1..=`max` up to isomorphism, each by its canonical
/// table, in order of size then table.
pub fn entities(max: u8) -> Vec<Table> {
    let mut out = Vec::new();
    for n in 1..=max {
        let classes: BTreeSet<Table> = Table::all(n).iter().map(Table::canonical).collect();
        out.extend(classes);
    }
    out
}

/// Maps of `points` points into themselves, each as its list of images, in
/// order.
fn maps(points: u8) -> Vec<Vec<u8>> {
    let count = (points as usize).pow(points as u32);
    (0..count)
        .map(|mut k| {
            (0..points)
                .map(|_| {
                    let v = (k % points as usize) as u8;
                    k /= points as usize;
                    v
                })
                .collect()
        })
        .collect()
}

/// One map, then the other.
fn then(f: &[u8], g: &[u8]) -> Vec<u8> {
    f.iter().map(|&p| g[p as usize]).collect()
}

/// The entities of the layer of maps: every set of maps of `points` points
/// closed under `then` and generated by one or two maps, as the table of
/// `then` on its elements. Sets equal up to renaming the points are taken
/// once; tables of up to `iso` elements are taken up to isomorphism, larger
/// ones as they come. In order of size, then table.
pub fn generated(points: u8, iso: u8) -> Vec<Table> {
    let all = maps(points);
    let mut closed: BTreeSet<Vec<Vec<u8>>> = BTreeSet::new();
    for i in 0..all.len() {
        for j in i..all.len() {
            // Every product of generators: each new element is followed by
            // each generator, so products of two known elements are never
            // formed (the idea of Froidure and Pin).
            let gens = [&all[i], &all[j]];
            let mut set: BTreeSet<Vec<u8>> = gens.iter().map(|g| g.to_vec()).collect();
            let mut fresh: Vec<Vec<u8>> = set.iter().cloned().collect();
            while let Some(f) = fresh.pop() {
                for g in gens {
                    let h = then(&f, g);
                    if set.insert(h.clone()) {
                        fresh.push(h);
                    }
                }
            }
            closed.insert(renamed(&set, points));
        }
    }
    let mut out: BTreeSet<Table> = BTreeSet::new();
    for set in closed {
        let n = set.len();
        let mut t = Table {
            n: n as u8,
            cells: vec![None; n * n],
        };
        for (a, f) in set.iter().enumerate() {
            for (b, g) in set.iter().enumerate() {
                let c = set.binary_search(&then(f, g)).unwrap();
                t.cells[a * n + b] = Some(c as u8);
            }
        }
        out.insert(if t.n <= iso { t.canonical() } else { t });
    }
    let mut out: Vec<Table> = out.into_iter().collect();
    out.sort_by(|a, b| (a.n, a).cmp(&(b.n, b)));
    out
}

/// The least form of a set of maps over renamings of the points.
fn renamed(set: &BTreeSet<Vec<u8>>, points: u8) -> Vec<Vec<u8>> {
    let mut perm: Vec<u8> = (0..points).collect();
    let mut best: Option<Vec<Vec<u8>>> = None;
    loop {
        let mut v: Vec<Vec<u8>> = set
            .iter()
            .map(|f| {
                let mut g = vec![0; f.len()];
                for (p, &q) in f.iter().enumerate() {
                    g[perm[p] as usize] = perm[q as usize];
                }
                g
            })
            .collect();
        v.sort();
        if best.as_ref().is_none_or(|b| v < *b) {
            best = Some(v);
        }
        if !next_perm(&mut perm) {
            return best.unwrap();
        }
    }
}

/// A set of entities, as bits.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Set(pub Vec<u64>);

impl Set {
    pub fn none(n: usize) -> Set {
        Set(vec![0; n.div_ceil(64).max(1)])
    }
    pub fn all(n: usize) -> Set {
        let mut s = Set::none(n);
        (0..n).for_each(|i| s.insert(i));
        s
    }
    pub fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    pub fn contains(&self, i: usize) -> bool {
        self.0[i / 64] >> (i % 64) & 1 == 1
    }
    pub fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }
    pub fn and(&self, o: &Set) -> Set {
        Set(self.0.iter().zip(&o.0).map(|(a, b)| a & b).collect())
    }
    fn or(&self, o: &Set) -> Set {
        Set(self.0.iter().zip(&o.0).map(|(a, b)| a | b).collect())
    }
    fn minus(&self, o: &Set) -> Set {
        Set(self.0.iter().zip(&o.0).map(|(a, b)| a & !b).collect())
    }
    pub fn within(&self, o: &Set) -> bool {
        self.0.iter().zip(&o.0).all(|(a, b)| a & !b == 0)
    }
    fn is_empty(&self) -> bool {
        self.0.iter().all(|&w| w == 0)
    }
}

/// Entities against laws: which entities each law holds on.
pub struct Atlas {
    pub entities: Vec<Table>,
    pub laws: Vec<Law>,
    pub holds: Vec<Set>,
}

impl Atlas {
    pub fn build(max: u8) -> Atlas {
        Atlas::with(max, &[]).0
    }

    /// The atlas of tables up to `max` together with the entities of
    /// another layer; and the set of that layer's entities in it.
    pub fn with(max: u8, layer: &[Table]) -> (Atlas, Set) {
        let mut entities = entities(max);
        let mut index = Vec::new();
        for t in layer {
            match entities.iter().position(|e| e == t) {
                Some(i) => index.push(i),
                None => {
                    entities.push(t.clone());
                    index.push(entities.len() - 1);
                }
            }
        }
        let mut own = Set::none(entities.len());
        index.into_iter().for_each(|i| own.insert(i));
        let laws = language();
        let holds = laws
            .iter()
            .map(|l| {
                let mut s = Set::none(entities.len());
                for (e, t) in entities.iter().enumerate() {
                    if l.holds(t) == Some(true) {
                        s.insert(e);
                    }
                }
                s
            })
            .collect();
        (
            Atlas {
                entities,
                laws,
                holds,
            },
            own,
        )
    }

    /// Every definition of `ext` within `among`: two or three laws holding
    /// on `ext` and on no other entity of `among`, none of them redundant.
    /// Laws holding on the same entities are taken once, by the first. Pairs
    /// first, then triples, each in law order.
    pub fn definitions(&self, ext: &Set, among: &Set) -> Vec<Vec<usize>> {
        let mut first: BTreeMap<&Set, usize> = BTreeMap::new();
        for l in self.content(ext) {
            first.entry(&self.holds[l]).or_insert(l);
        }
        let mut ls: Vec<usize> = first.into_values().collect();
        ls.sort();
        let cut = |s: Set| s.and(among) == *ext;
        let h = |i: usize| &self.holds[ls[i]];
        let mut out = Vec::new();
        for i in 0..ls.len() {
            for j in i + 1..ls.len() {
                if cut(h(i).and(h(j))) {
                    out.push(vec![ls[i], ls[j]]);
                }
            }
        }
        for i in 0..ls.len() {
            for j in i + 1..ls.len() {
                let ij = h(i).and(h(j));
                if cut(ij.clone()) {
                    continue;
                }
                for k in j + 1..ls.len() {
                    if cut(ij.and(h(k))) && !cut(h(i).and(h(k))) && !cut(h(j).and(h(k))) {
                        out.push(vec![ls[i], ls[j], ls[k]]);
                    }
                }
            }
        }
        out
    }

    /// The most specific of `defs`: those where no law can be swapped for a
    /// law holding on strictly fewer entities that still holds on every
    /// entity of `seen` (the S boundary of a version space).
    pub fn specific<'d>(&self, defs: &'d [Vec<usize>], seen: &Set) -> Vec<&'d Vec<usize>> {
        let stronger = |l: usize| {
            (0..self.laws.len()).any(|m| {
                self.holds[m] != self.holds[l]
                    && self.holds[m].within(&self.holds[l])
                    && seen.within(&self.holds[m])
            })
        };
        defs.iter()
            .filter(|d| !d.iter().any(|&l| stronger(l)))
            .collect()
    }

    /// Definitions gathered by the entities of `layer` they hold on: one
    /// branch per such set, widest first.
    pub fn branches(&self, defs: &[Vec<usize>], layer: &Set) -> Vec<(Set, Vec<Vec<usize>>)> {
        let mut by: BTreeMap<Set, Vec<Vec<usize>>> = BTreeMap::new();
        for d in defs {
            by.entry(self.extent(d).and(layer))
                .or_default()
                .push(d.clone());
        }
        let mut out: Vec<(Set, Vec<Vec<usize>>)> = by.into_iter().collect();
        out.sort_by(|a, b| b.0.count().cmp(&a.0.count()).then(a.0.cmp(&b.0)));
        out
    }

    /// Laws holding on every entity of `ext`.
    pub fn content(&self, ext: &Set) -> Vec<usize> {
        (0..self.laws.len())
            .filter(|&l| ext.within(&self.holds[l]))
            .collect()
    }

    /// Entities on which every law of `laws` holds.
    pub fn extent(&self, laws: &[usize]) -> Set {
        laws.iter()
            .fold(Set::all(self.entities.len()), |m, &l| m.and(&self.holds[l]))
    }

    /// A shortest set of laws, up to three, that holds on `ext` and on no
    /// other entity; the first in law order among the shortest. Empty when
    /// `ext` is not closed or needs more.
    pub fn definition(&self, ext: &Set) -> Vec<usize> {
        let outside = Set::all(self.entities.len()).minus(ext);
        let mut by_sig: BTreeMap<Set, usize> = BTreeMap::new();
        for l in self.content(ext) {
            let sig = outside.minus(&self.holds[l]);
            if !sig.is_empty() {
                by_sig.entry(sig).or_insert(l);
            }
        }
        let sigs: Vec<(Set, usize)> = by_sig.into_iter().collect();
        let pick = |ix: &[usize]| {
            let mut v: Vec<usize> = ix.iter().map(|&i| sigs[i].1).collect();
            v.sort();
            v
        };
        let mut best: Option<Vec<usize>> = None;
        let keep = |c: Vec<usize>, best: &mut Option<Vec<usize>>| {
            if best.as_ref().is_none_or(|b| c < *b) {
                *best = Some(c);
            }
        };
        for (i, (s, _)) in sigs.iter().enumerate() {
            if *s == outside {
                keep(pick(&[i]), &mut best);
            }
        }
        if let Some(b) = best {
            return b;
        }
        for i in 0..sigs.len() {
            for j in i + 1..sigs.len() {
                if sigs[i].0.or(&sigs[j].0) == outside {
                    keep(pick(&[i, j]), &mut best);
                }
            }
        }
        if let Some(b) = best {
            return b;
        }
        for i in 0..sigs.len() {
            for j in i + 1..sigs.len() {
                let ij = sigs[i].0.or(&sigs[j].0);
                for (k, (sk, _)) in sigs.iter().enumerate().skip(j + 1) {
                    if ij.or(sk) == outside {
                        keep(pick(&[i, j, k]), &mut best);
                    }
                }
            }
        }
        best.unwrap_or_default()
    }
}

/// Models on `n` elements where every law of `yes` holds and every law of
/// `no` fails, up to isomorphism, by canonical table; and the number of
/// search nodes.
///
/// Each empty cell keeps the values it may still take. After every move a
/// value is struck when the laws, read on the table with these sets, fail
/// with it; a cell left with one value takes it. The next cell to fill is
/// the one with fewest values left. Elements not yet mentioned in the table
/// are interchangeable, so only the least of them is tried.
pub fn models(n: u8, yes: &[&Law], no: &[&Law]) -> (Vec<Table>, usize) {
    let mut s = Search {
        t: Table {
            n,
            cells: vec![None; (n as usize).pow(2)],
        },
        dom: vec![(1u16 << n) - 1; (n as usize).pow(2)],
        yes,
        no,
        found: BTreeSet::new(),
        nodes: 0,
    };
    s.go();
    (s.found.into_iter().collect(), s.nodes)
}

struct Search<'a> {
    t: Table,
    dom: Vec<u16>,
    yes: &'a [&'a Law],
    no: &'a [&'a Law],
    found: BTreeSet<Table>,
    nodes: usize,
}

impl Search<'_> {
    fn dead(&self) -> bool {
        self.yes
            .iter()
            .any(|l| l.holds_in(&self.t, &self.dom) == Some(false))
            || self
                .no
                .iter()
                .any(|l| l.holds_in(&self.t, &self.dom) == Some(true))
    }

    /// Strikes values until nothing changes; false when a cell has none.
    fn narrow(&mut self) -> bool {
        loop {
            let mut changed = false;
            for c in 0..self.t.cells.len() {
                if self.t.cells[c].is_some() {
                    continue;
                }
                for v in 0..self.t.n {
                    if self.dom[c] >> v & 1 == 0 {
                        continue;
                    }
                    self.t.cells[c] = Some(v);
                    if self.dead() {
                        self.dom[c] &= !(1 << v);
                        changed = true;
                    }
                    self.t.cells[c] = None;
                }
                match self.dom[c].count_ones() {
                    0 => return false,
                    1 => self.t.cells[c] = Some(self.dom[c].trailing_zeros() as u8),
                    _ => {}
                }
            }
            if !changed {
                return !self.dead();
            }
        }
    }

    fn go(&mut self) {
        self.nodes += 1;
        let (cells, dom) = (self.t.cells.clone(), self.dom.clone());
        if self.narrow() {
            let n = self.t.n as usize;
            let next = (0..n * n)
                .filter(|&c| self.t.cells[c].is_none())
                .min_by_key(|&c| (self.dom[c].count_ones(), c));
            match next {
                None => {
                    self.found.insert(self.t.canonical());
                }
                Some(c) => {
                    let mut seen = 0u16;
                    for (k, v) in self.t.cells.iter().enumerate() {
                        if let Some(v) = v {
                            seen |= 1 << (k / n) | 1 << (k % n) | 1 << v;
                        }
                    }
                    seen |= 1 << (c / n) | 1 << (c % n);
                    let fresh = (!seen).trailing_zeros();
                    for v in 0..self.t.n {
                        let ok = seen >> v & 1 == 1 || v as u32 == fresh;
                        if !ok || self.dom[c] >> v & 1 == 0 {
                            continue;
                        }
                        let (cells, dom) = (self.t.cells.clone(), self.dom.clone());
                        self.t.cells[c] = Some(v);
                        self.dom[c] = 1 << v;
                        self.go();
                        (self.t.cells, self.dom) = (cells, dom);
                    }
                }
            }
        }
        (self.t.cells, self.dom) = (cells, dom);
    }
}

/// The same as `models`, by the CDCL solver of `sat.rs`; the number is of
/// conflicts. A cell value is a variable "cell (a, b) is v"; a law for all
/// values becomes one clause per value of its variables and of its inner
/// cells; a variable that "there is" becomes an unknown function of the
/// variables "for all" before it (Skolem), as in the finite model finder
/// Paradox. Isomorphic tables are cut by the least number rule as clauses:
/// in the order of cells by their larger index, a value may exceed every
/// element mentioned before by one at most. Every model found is ruled out
/// by one more clause, and the search goes on until there is none.
pub fn models_sat(n: u8, yes: &[&Law], no: &[&Law]) -> (Vec<Table>, usize) {
    let mut e = Enc::new(n as usize);
    for l in yes {
        e.law(&l.prefix, &l.left, &l.right, true);
    }
    for l in no {
        let prefix: Vec<(u8, bool)> = l.prefix.iter().map(|&(v, all)| (v, !all)).collect();
        e.law(&prefix, &l.left, &l.right, false);
    }
    e.least_numbers();
    let n = n as usize;
    let mut found = BTreeSet::new();
    while e.s.solve() {
        let mut t = Table {
            n: n as u8,
            cells: vec![None; n * n],
        };
        let mut block = Vec::with_capacity(n * n);
        for c in 0..n * n {
            let v = (0..n)
                .find(|&v| e.s.model(e.cell(c / n, c % n, v)))
                .unwrap();
            t.cells[c] = Some(v as u8);
            block.push(Lit::neg(e.cell(c / n, c % n, v)));
        }
        found.insert(t.canonical());
        e.s.add(&block);
    }
    (found.into_iter().collect(), e.s.conflicts)
}

struct Enc {
    s: Solver,
    n: usize,
}

/// A value a term may take, and the literals that force it.
type Opt = (usize, Vec<Lit>);

impl Enc {
    fn new(n: usize) -> Enc {
        let mut s = Solver::new();
        for _ in 0..n * n * n {
            s.var();
        }
        let mut e = Enc { s, n };
        for a in 0..n {
            for b in 0..n {
                e.one_of((0..n).map(|v| e.cell(a, b, v)).collect());
            }
        }
        e
    }

    fn cell(&self, a: usize, b: usize, v: usize) -> usize {
        (a * self.n + b) * self.n + v
    }

    fn one_of(&mut self, vars: Vec<usize>) {
        self.s
            .add(&vars.iter().map(|&v| Lit::pos(v)).collect::<Vec<_>>());
        for i in 0..vars.len() {
            for j in i + 1..vars.len() {
                self.s.add(&[Lit::neg(vars[i]), Lit::neg(vars[j])]);
            }
        }
    }

    /// The equation (or, with `eq` false, its negation) under the prefix.
    fn law(&mut self, prefix: &[(u8, bool)], left: &Term, right: &Term, eq: bool) {
        let n = self.n;
        // For each variable that "there is": the variables "for all" before
        // it and the first of its n^k * n solver variables.
        let mut sk: [Option<(Vec<u8>, usize)>; 3] = [None, None, None];
        let mut outer: Vec<u8> = Vec::new();
        for &(v, all) in prefix {
            if all {
                outer.push(v);
            } else {
                let tuples = n.pow(outer.len() as u32);
                let base = self.s_vars(tuples * n);
                for t in 0..tuples {
                    self.one_of((0..n).map(|w| base + t * n + w).collect());
                }
                sk[v as usize] = Some((outer.clone(), base));
            }
        }
        let total = n.pow(outer.len() as u32);
        for k in 0..total {
            let mut env = [0usize; 3];
            let mut r = k;
            for &v in &outer {
                env[v as usize] = r % n;
                r /= n;
            }
            let ls = self.roots(left, &env, &sk);
            let rs = self.roots(right, &env, &sk);
            for (l, pl) in &ls {
                for (r, pr) in &rs {
                    let mut base: Vec<Lit> = pl.iter().chain(pr).map(|&x| !x).collect();
                    match (l, r) {
                        (Root::Cell(la, lb), Root::Cell(ra, rb)) => {
                            for w in 0..n {
                                let mut c = base.clone();
                                c.push(Lit::neg(self.cell(*la, *lb, w)));
                                c.push(if eq {
                                    Lit::pos(self.cell(*ra, *rb, w))
                                } else {
                                    Lit::neg(self.cell(*ra, *rb, w))
                                });
                                self.s.add(&c);
                            }
                        }
                        (Root::Cell(a, b), Root::Val(v)) | (Root::Val(v), Root::Cell(a, b)) => {
                            let x = self.cell(*a, *b, *v);
                            base.push(if eq { Lit::pos(x) } else { Lit::neg(x) });
                            self.s.add(&base);
                        }
                        (Root::Val(a), Root::Val(b)) => {
                            if (a == b) != eq {
                                self.s.add(&base);
                            }
                        }
                    }
                }
            }
        }
    }

    fn s_vars(&mut self, k: usize) -> usize {
        let base = self.s.var();
        for _ in 1..k {
            self.s.var();
        }
        base
    }

    fn opts(&self, t: &Term, env: &[usize; 3], sk: &[Option<(Vec<u8>, usize)>; 3]) -> Vec<Opt> {
        match t {
            Term::Var(v) => match &sk[*v as usize] {
                None => vec![(env[*v as usize], vec![])],
                Some((deps, base)) => {
                    let tuple = deps
                        .iter()
                        .rev()
                        .fold(0, |acc, &d| acc * self.n + env[d as usize]);
                    (0..self.n)
                        .map(|w| (w, vec![Lit::pos(base + tuple * self.n + w)]))
                        .collect()
                }
            },
            Term::Op(a, b) => {
                let mut out = Vec::new();
                for (va, pa) in self.opts(a, env, sk) {
                    for (vb, pb) in self.opts(b, env, sk) {
                        for w in 0..self.n {
                            let mut p = pa.clone();
                            p.extend(&pb);
                            p.push(Lit::pos(self.cell(va, vb, w)));
                            out.push((w, p));
                        }
                    }
                }
                out
            }
        }
    }

    /// The top of a term: a cell whose value is left open, or a value.
    fn roots(
        &self,
        t: &Term,
        env: &[usize; 3],
        sk: &[Option<(Vec<u8>, usize)>; 3],
    ) -> Vec<(Root, Vec<Lit>)> {
        match t {
            Term::Op(a, b) => {
                let mut out = Vec::new();
                for (va, pa) in self.opts(a, env, sk) {
                    for (vb, pb) in self.opts(b, env, sk) {
                        let mut p = pa.clone();
                        p.extend(&pb);
                        out.push((Root::Cell(va, vb), p));
                    }
                }
                out
            }
            _ => self
                .opts(t, env, sk)
                .into_iter()
                .map(|(v, p)| (Root::Val(v), p))
                .collect(),
        }
    }

    /// The least number rule. `g(k, j)`: some cell before the k-th holds a
    /// value of at least j.
    fn least_numbers(&mut self) {
        let n = self.n;
        if n < 3 {
            return;
        }
        let mut order: Vec<(usize, usize)> =
            (0..n).flat_map(|a| (0..n).map(move |b| (a, b))).collect();
        order.sort_by_key(|&(a, b)| (a.max(b), a, b));
        let base = self.s_vars((order.len() + 1) * n);
        let g = |k: usize, j: usize| base + k * n + j;
        for j in 1..n {
            self.s.add(&[Lit::neg(g(0, j))]);
        }
        for (k, &(a, b)) in order.iter().enumerate() {
            for j in 1..n {
                let mut c = vec![Lit::neg(g(k + 1, j)), Lit::pos(g(k, j))];
                c.extend((j..n).map(|v| Lit::pos(self.cell(a, b, v))));
                self.s.add(&c);
            }
            for v in a.max(b) + 2..n {
                self.s
                    .add(&[Lit::neg(self.cell(a, b, v)), Lit::pos(g(k, v - 1))]);
            }
        }
    }
}

enum Root {
    Cell(usize, usize),
    Val(usize),
}

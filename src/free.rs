//! Laws as elements of a free entity (`docs/impl/atlas.md` §10).
//!
//! The free entity on k generators to depth d is made by closure, like the
//! layer of maps: the generators, then every product of two elements made
//! so far, while the depth allows. Nothing in it is glued, and a product
//! deeper than d is not defined. A law is a pair of its elements under a
//! prefix of quantifiers over the generators. A law holds on an entity when
//! every map of the generators into it, carried over to the free entity
//! (each element is the product of its two parts), sends both elements to
//! one. Laws that follow from others are found by Birkhoff's rules: an
//! instance is a map of the generators into the free entity itself; equal
//! parts make equal products; the rest is union of classes (congruence
//! closure).

use crate::atlas::{Table, Term};
use std::collections::BTreeMap;

pub struct Free {
    pub gens: u32,
    /// The two parts of each element; none for a generator.
    pub parts: Vec<Option<(u32, u32)>>,
    pub depth: Vec<u8>,
    index: BTreeMap<(u32, u32), u32>,
}

impl Free {
    /// Generators first, then each round every product of two elements
    /// made before it, in order; up to `depth` rounds.
    pub fn new(gens: u32, depth: u8) -> Free {
        let mut f = Free {
            gens,
            parts: vec![None; gens as usize],
            depth: vec![0; gens as usize],
            index: BTreeMap::new(),
        };
        for _ in 0..depth {
            let made = f.parts.len() as u32;
            for a in 0..made {
                for b in 0..made {
                    if !f.index.contains_key(&(a, b)) {
                        let e = f.parts.len() as u32;
                        f.index.insert((a, b), e);
                        f.parts.push(Some((a, b)));
                        f.depth
                            .push(1 + f.depth[a as usize].max(f.depth[b as usize]));
                    }
                }
            }
        }
        f
    }

    pub fn len(&self) -> usize {
        self.parts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub fn product(&self, a: u32, b: u32) -> Option<u32> {
        self.index.get(&(a, b)).copied()
    }

    /// The image of element `e` under the map sending generator g to
    /// `to[g]`, carried over by the operation `op`.
    pub fn image<T: Copy>(&self, e: u32, to: &[T], op: &impl Fn(T, T) -> Option<T>) -> Option<T> {
        match self.parts[e as usize] {
            None => Some(to[e as usize]),
            Some((a, b)) => op(self.image(a, to, op)?, self.image(b, to, op)?),
        }
    }

    /// The deepest place at which generator `g` occurs in `e`, if it does.
    pub fn place(&self, e: u32, g: u32) -> Option<u8> {
        match self.parts[e as usize] {
            None => (e == g).then_some(0),
            Some((a, b)) => self.place(a, g).max(self.place(b, g)).map(|d| d + 1),
        }
    }

    pub fn term(&self, e: u32) -> Term {
        match self.parts[e as usize] {
            None => Term::Var(e as u8),
            Some((a, b)) => Term::Op(Box::new(self.term(a)), Box::new(self.term(b))),
        }
    }
}

/// A law: a pair of elements of the free entity under a prefix; `true` in
/// the prefix is "for all".
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Eq {
    pub prefix: Vec<(u8, bool)>,
    pub left: u32,
    pub right: u32,
}

impl Eq {
    /// Whether the law holds on a full table.
    pub fn holds(&self, f: &Free, t: &Table) -> bool {
        let mut env = vec![0u8; f.gens as usize];
        self.go(f, t, 0, &mut env)
    }

    fn go(&self, f: &Free, t: &Table, i: usize, env: &mut Vec<u8>) -> bool {
        let Some(&(g, all)) = self.prefix.get(i) else {
            let op = |a: u8, b: u8| t.get(a, b);
            return f.image(self.left, env, &op) == f.image(self.right, env, &op);
        };
        for v in 0..t.n {
            env[g as usize] = v;
            if self.go(f, t, i + 1, env) != all {
                return !all;
            }
        }
        all
    }

    pub fn show(&self, f: &Free) -> String {
        crate::atlas::Law {
            prefix: self.prefix.clone(),
            left: f.term(self.left),
            right: f.term(self.right),
        }
        .to_string()
    }

    /// The least form over renamings of the generators (each carried over
    /// to the free entity) and the two sides; neighbouring quantifiers of
    /// one kind commute, so each run of them is sorted.
    fn normal(&self, f: &Free, renamings: &[Vec<u32>]) -> Eq {
        let op = |a: u32, b: u32| f.product(a, b);
        let mut best: Option<Eq> = None;
        for to in renamings {
            let mut prefix: Vec<(u8, bool)> = self
                .prefix
                .iter()
                .map(|&(g, a)| (to[g as usize] as u8, a))
                .collect();
            let mut i = 0;
            while i < prefix.len() {
                let j = (i..prefix.len())
                    .find(|&j| prefix[j].1 != prefix[i].1)
                    .unwrap_or(prefix.len());
                prefix[i..j].sort();
                i = j;
            }
            let l = f.image(self.left, to, &op).unwrap();
            let r = f.image(self.right, to, &op).unwrap();
            for (left, right) in [(l, r), (r, l)] {
                let c = Eq {
                    prefix: prefix.clone(),
                    left,
                    right,
                };
                if best.as_ref().is_none_or(|b| c < *b) {
                    best = Some(c);
                }
            }
        }
        best.unwrap()
    }
}

/// The language as pairs of elements of the free entity on three
/// generators to depth 2: every pair of distinct elements for all values,
/// and every pair of distinct elements of depth at most 1 under every
/// prefix of quantifiers over their generators in every order; each law
/// once up to renaming, sides and commuting quantifiers.
pub fn language(f: &Free) -> Vec<Eq> {
    let n = f.gens;
    let renamings: Vec<Vec<u32>> = perms(n);
    let mut out = std::collections::BTreeSet::new();
    let gens_of = |a: u32, b: u32| -> Vec<u8> {
        (0..n)
            .filter(|&g| f.place(a, g).is_some() || f.place(b, g).is_some())
            .map(|g| g as u8)
            .collect()
    };
    for a in 0..f.len() as u32 {
        for b in a + 1..f.len() as u32 {
            let vs = gens_of(a, b);
            let mut prefixes = vec![vs.iter().map(|&g| (g, true)).collect::<Vec<_>>()];
            if f.depth[a as usize] <= 1 && f.depth[b as usize] <= 1 {
                for order in perms(vs.len() as u32) {
                    for mask in 0..1u32 << vs.len() {
                        prefixes.push(
                            order
                                .iter()
                                .enumerate()
                                .map(|(k, &o)| (vs[o as usize], mask >> k & 1 == 0))
                                .collect(),
                        );
                    }
                }
            }
            for prefix in prefixes {
                out.insert(
                    Eq {
                        prefix,
                        left: a,
                        right: b,
                    }
                    .normal(f, &renamings),
                );
            }
        }
    }
    out.into_iter().collect()
}

fn perms(n: u32) -> Vec<Vec<u32>> {
    let mut p: Vec<u32> = (0..n).collect();
    let mut out = vec![p.clone()];
    loop {
        let Some(i) = (1..p.len()).rev().find(|&i| p[i - 1] < p[i]) else {
            return out;
        };
        let j = (i..p.len()).rev().find(|&j| p[j] > p[i - 1]).unwrap();
        p.swap(i - 1, j);
        p[i..].reverse();
        out.push(p.clone());
    }
}

/// What follows from laws "for all" on a free entity: classes of its
/// elements made equal by Birkhoff's rules within its depth.
pub struct Derived {
    pub free: Free,
    up: Vec<u32>,
}

impl Derived {
    /// `axioms` are pairs of elements of `free`, read for all values.
    pub fn new(free: Free, axioms: &[(u32, u32)]) -> Derived {
        let mut d = Derived {
            up: (0..free.len() as u32).collect(),
            free,
        };
        let f = &d.free;
        let op = |a: u32, b: u32| f.product(a, b);
        let mut pairs = Vec::new();
        for &(l, r) in axioms {
            // Each generator may take any element shallow enough for both
            // sides to stay inside the free entity.
            let room: Vec<Vec<u32>> = (0..f.gens)
                .map(|g| match f.place(l, g).max(f.place(r, g)) {
                    None => vec![0],
                    Some(p) => {
                        let max = f.depth.iter().copied().max().unwrap() - p;
                        (0..f.len() as u32)
                            .filter(|&e| f.depth[e as usize] <= max)
                            .collect()
                    }
                })
                .collect();
            let mut pick = vec![0usize; f.gens as usize];
            'all: loop {
                let to: Vec<u32> = (0..f.gens as usize).map(|g| room[g][pick[g]]).collect();
                if let (Some(a), Some(b)) = (f.image(l, &to, &op), f.image(r, &to, &op)) {
                    pairs.push((a, b));
                }
                for g in 0..f.gens as usize {
                    pick[g] += 1;
                    if pick[g] < room[g].len() {
                        continue 'all;
                    }
                    pick[g] = 0;
                }
                break;
            }
        }
        for (a, b) in pairs {
            d.union(a, b);
        }
        // Equal parts make equal products, until nothing changes.
        loop {
            let mut seen: BTreeMap<(u32, u32), u32> = BTreeMap::new();
            let mut merge = Vec::new();
            for e in 0..d.free.len() as u32 {
                if let Some((a, b)) = d.free.parts[e as usize] {
                    let key = (d.find(a), d.find(b));
                    match seen.get(&key) {
                        Some(&o) if d.find(o) != d.find(e) => merge.push((o, e)),
                        Some(_) => {}
                        None => {
                            seen.insert(key, e);
                        }
                    }
                }
            }
            if merge.is_empty() {
                return d;
            }
            for (a, b) in merge {
                d.union(a, b);
            }
        }
    }

    pub fn find(&self, mut e: u32) -> u32 {
        while self.up[e as usize] != e {
            e = self.up[e as usize];
        }
        e
    }

    fn union(&mut self, a: u32, b: u32) {
        let (a, b) = (self.find(a), self.find(b));
        // The lower element stays the root: the result does not depend on
        // the order of merging.
        if a != b {
            let (lo, hi) = (a.min(b), a.max(b));
            self.up[hi as usize] = lo;
        }
    }

    pub fn equal(&self, a: u32, b: u32) -> bool {
        self.find(a) == self.find(b)
    }
}

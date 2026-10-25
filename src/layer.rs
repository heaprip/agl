//! Relations between relations (H75, `docs/impl/relations.md`, stage A).
//!
//! A query over two holes R and S, glued from one atom of each the way the
//! bank glues its parts, read on every pair of relations of the world gives
//! a relation between relations: g(r, s, t) when the query on r and s has
//! the extent of t. That one pair has one t follows from logic (the extent
//! of a query is fixed by its parts); that every pair has one is a property
//! of the world (it holds every extent). Whether g(g(R, S), T) and
//! g(R, g(S, T)), or g(R, S) and g(S, R), are equal is decided by logic
//! (homomorphisms of queries both ways, Chandra and Merlin); where logic
//! says no, the frozen query is a world that shows it. No property is named
//! here.

use crate::bank::Ext;
use std::collections::BTreeMap;
use std::fmt::Write as _;

/// Ways to identify the ends of the first atom (0, 1) with the ends of the
/// second (2, 3), as in the bank.
const MERGES: [&[(usize, usize)]; 7] = [
    &[],
    &[(0, 2)],
    &[(0, 3)],
    &[(1, 2)],
    &[(1, 3)],
    &[(0, 2), (1, 3)],
    &[(0, 3), (1, 2)],
];

/// A conjunctive query over holes: atoms (hole, u, v) over variables, and a
/// pair of heads.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Query {
    pub atoms: Vec<(u8, u8, u8)>,
    pub vars: u8,
    pub head: (u8, u8),
}

impl Query {
    /// The query of one hole: h(x, y).
    pub fn hole(h: u8) -> Query {
        Query {
            atoms: vec![(h, 0, 1)],
            vars: 2,
            head: (0, 1),
        }
    }

    /// Every query of one gluing of R(0) and S(1): each merge of their
    /// ends, each ordered pair of heads; once each up to logic.
    pub fn gluings() -> Vec<Query> {
        let mut out: Vec<Query> = Vec::new();
        for m in MERGES {
            let mut block = [0usize, 1, 2, 3];
            for &(p, q) in m {
                block[q] = block[p];
            }
            let mut ends: Vec<usize> = block.to_vec();
            ends.sort();
            ends.dedup();
            let atoms = [(0u8, block[0], block[1]), (1u8, block[2], block[3])];
            for &h0 in &ends {
                for &h1 in &ends {
                    let q = normal(&atoms, (h0, h1));
                    if !out.iter().any(|o| o.same(&q)) {
                        out.push(q);
                    }
                }
            }
        }
        out.sort();
        out
    }

    /// The holes of `self` replaced by queries: each atom of hole h by a
    /// fresh copy of `with[h]` whose heads are the atom's ends.
    pub fn substitute(&self, with: &[Query]) -> Query {
        let mut atoms: Vec<(u8, usize, usize)> = Vec::new();
        let mut same: Vec<(usize, usize)> = Vec::new();
        let mut next = self.vars as usize;
        for &(h, u, v) in &self.atoms {
            let w = &with[h as usize];
            let base = next;
            next += w.vars as usize;
            atoms.extend(
                w.atoms
                    .iter()
                    .map(|&(g, p, q)| (g, base + p as usize, base + q as usize)),
            );
            same.push((u as usize, base + w.head.0 as usize));
            same.push((v as usize, base + w.head.1 as usize));
        }
        let mut up: Vec<usize> = (0..next).collect();
        fn find(up: &mut [usize], mut x: usize) -> usize {
            while up[x] != x {
                x = up[x];
            }
            x
        }
        for (a, b) in same {
            let (a, b) = (find(&mut up, a), find(&mut up, b));
            up[a.max(b)] = a.min(b);
        }
        let atoms: Vec<(u8, usize, usize)> = atoms
            .into_iter()
            .map(|(g, p, q)| (g, find(&mut up, p), find(&mut up, q)))
            .collect();
        let head = (
            find(&mut up, self.head.0 as usize),
            find(&mut up, self.head.1 as usize),
        );
        normal(&atoms, head)
    }

    /// Holes renumbered: hole h becomes `to[h]`.
    pub fn relabel(&self, to: &[u8]) -> Query {
        let atoms: Vec<(u8, usize, usize)> = self
            .atoms
            .iter()
            .map(|&(h, u, v)| (to[h as usize], u as usize, v as usize))
            .collect();
        normal(&atoms, (self.head.0 as usize, self.head.1 as usize))
    }

    /// Whether logic gives every answer of `self` as an answer of `o`.
    pub fn within(&self, o: &Query) -> bool {
        hom(o, &self.atoms, self.head).is_some()
    }

    pub fn same(&self, o: &Query) -> bool {
        self.within(o) && o.within(self)
    }

    /// The extent on relations given for the holes.
    pub fn eval(&self, holes: &[&Ext]) -> Ext {
        let n = holes[0].n();
        let mut out = Ext::empty(n);
        let mut v = vec![0usize; self.vars as usize];
        'all: loop {
            if self
                .atoms
                .iter()
                .all(|&(h, a, b)| holes[h as usize].get(v[a as usize], v[b as usize]))
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

    /// The query frozen into a world: its variables as points, each hole
    /// the relation of its atoms (Chandra and Merlin's canonical database).
    pub fn frozen(&self, holes: usize) -> Vec<Ext> {
        let n = self.vars as usize;
        let mut out = vec![Ext::empty(n); holes];
        for &(h, a, b) in &self.atoms {
            out[h as usize].set(a as usize, b as usize);
        }
        out
    }
}

/// The core of a query, relabelled: heads first, then variables by first
/// appearance; atoms sorted.
fn normal(atoms: &[(u8, usize, usize)], h: (usize, usize)) -> Query {
    let mut q = relabel(atoms, h);
    'shrink: loop {
        for i in 0..q.atoms.len() {
            let rest: Vec<(u8, u8, u8)> = q
                .atoms
                .iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(_, &a)| a)
                .collect();
            if let Some(map) = hom(&q, &rest, q.head) {
                let atoms: Vec<(u8, usize, usize)> = q
                    .atoms
                    .iter()
                    .map(|&(g, u, v)| (g, map[u as usize] as usize, map[v as usize] as usize))
                    .collect();
                q = relabel(&atoms, (q.head.0 as usize, q.head.1 as usize));
                continue 'shrink;
            }
        }
        return q;
    }
}

fn relabel(atoms: &[(u8, usize, usize)], h: (usize, usize)) -> Query {
    let mut ids: BTreeMap<usize, u8> = BTreeMap::new();
    let id = |x: usize, ids: &mut BTreeMap<usize, u8>| {
        let k = ids.len() as u8;
        *ids.entry(x).or_insert(k)
    };
    let head = (id(h.0, &mut ids), id(h.1, &mut ids));
    let mut out: Vec<(u8, u8, u8)> = atoms
        .iter()
        .map(|&(g, u, v)| (g, id(u, &mut ids), id(v, &mut ids)))
        .collect();
    out.sort();
    out.dedup();
    Query {
        atoms: out,
        vars: ids.len() as u8,
        head,
    }
}

/// A map of the variables of `p` sending its heads to `head` and each atom
/// to an atom of `atoms` with the same hole.
fn hom(p: &Query, atoms: &[(u8, u8, u8)], head: (u8, u8)) -> Option<Vec<u8>> {
    const FREE: u8 = u8::MAX;
    let mut map = vec![FREE; p.vars as usize];
    for (x, y) in [(p.head.0, head.0), (p.head.1, head.1)] {
        match map[x as usize] {
            FREE => map[x as usize] = y,
            z if z != y => return None,
            _ => {}
        }
    }
    fn go(i: usize, p: &[(u8, u8, u8)], q: &[(u8, u8, u8)], map: &mut Vec<u8>) -> bool {
        let Some(&(h, u, v)) = p.get(i) else {
            return true;
        };
        for &(g, x, y) in q {
            let (mu, mv) = (map[u as usize], map[v as usize]);
            if g != h || (mu != FREE && mu != x) || (mv != FREE && mv != y) || (u == v && x != y) {
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

const HOLES: &[&str] = &["R", "S", "T"];
const VARS: &[&str] = &["x", "y", "a", "b", "c", "d", "e", "f"];

impl std::fmt::Display for Query {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = |i: u8| VARS.get(i as usize).copied().unwrap_or("?");
        write!(f, "{{{},{} |", v(self.head.0), v(self.head.1))?;
        for (i, &(h, a, b)) in self.atoms.iter().enumerate() {
            let sep = if i == 0 { " " } else { ", " };
            write!(f, "{sep}{}({},{})", HOLES[h as usize], v(a), v(b))?;
        }
        write!(f, "}}")
    }
}

/// An expression in one gluing over the holes R, S, T: a hole, or the
/// gluing of two expressions.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Hole(u8),
    Glue(Box<Term>, Box<Term>),
}

impl Term {
    fn depth(&self) -> usize {
        match self {
            Term::Hole(_) => 0,
            Term::Glue(a, b) => 1 + a.depth().max(b.depth()),
        }
    }

    /// Every expression of depth at most 2 over three holes, shallow first.
    pub fn all() -> Vec<Term> {
        let mut out: Vec<Term> = (0..3).map(Term::Hole).collect();
        for _ in 0..2 {
            let made = out.clone();
            for a in &made {
                for b in &made {
                    let t = Term::Glue(Box::new(a.clone()), Box::new(b.clone()));
                    if !out.contains(&t) {
                        out.push(t);
                    }
                }
            }
        }
        out.sort_by_key(|t| (t.depth(), t.clone()));
        out
    }

    pub fn query(&self, g: &Query) -> Query {
        match self {
            Term::Hole(h) => Query::hole(*h),
            Term::Glue(a, b) => g.substitute(&[a.query(g), b.query(g)]),
        }
    }

    fn rename(&self, to: &[u8]) -> Term {
        match self {
            Term::Hole(h) => Term::Hole(to[*h as usize]),
            Term::Glue(a, b) => Term::Glue(Box::new(a.rename(to)), Box::new(b.rename(to))),
        }
    }

    /// The relation the expression names on relations `at`, by the table of
    /// the gluing; none where the world lacks the extent.
    fn value(&self, table: &[Option<u32>], k: usize, at: [u32; 3]) -> Option<u32> {
        match self {
            Term::Hole(h) => Some(at[*h as usize]),
            Term::Glue(a, b) => {
                let (a, b) = (a.value(table, k, at)?, b.value(table, k, at)?);
                table[a as usize * k + b as usize]
            }
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Hole(h) => write!(f, "{}", HOLES[*h as usize]),
            Term::Glue(a, b) => write!(f, "({a}∘{b})"),
        }
    }
}

/// A coincidence of two expressions: what logic says (equal, or the
/// number of points of the frozen query showing not) and what each world
/// says.
pub struct Law {
    pub left: Term,
    pub right: Term,
    pub logic: Result<(), usize>,
    /// For each world by its number of points: equal on every triple of
    /// its relations where both are defined; none if not checked (logic
    /// already gives it).
    pub worlds: Vec<(usize, Option<bool>)>,
}

/// What was found for one gluing.
pub struct Found {
    pub query: Query,
    /// Whether each world holds the extent for every pair.
    pub total: Vec<(usize, bool)>,
    pub laws: Vec<Law>,
}

/// Logic for two expressions: equal both ways, or the size of a world
/// showing not.
fn by_logic(a: &Query, b: &Query) -> Result<(), usize> {
    match (a.within(b), b.within(a)) {
        (true, true) => Ok(()),
        (false, _) => Err(a.vars as usize),
        (true, false) => Err(b.vars as usize),
    }
}

/// The least form of a pair of expressions over renamings of the holes and
/// the two sides.
fn canonical(l: &Term, r: &Term) -> (Term, Term) {
    let mut best: Option<(Term, Term)> = None;
    for to in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        let (a, b) = (l.rename(&to), r.rename(&to));
        for c in [(a.clone(), b.clone()), (b, a)] {
            if best.as_ref().is_none_or(|x| c < *x) {
                best = Some(c);
            }
        }
    }
    best.unwrap()
}

/// Whether two expressions name one relation on every triple of the
/// world's relations where both are defined.
pub fn holds(t: &[Option<u32>], k: usize, l: &Term, r: &Term) -> bool {
    let k32 = k as u32;
    for a in 0..k32 {
        for b in 0..k32 {
            for c in 0..k32 {
                let (x, y) = (l.value(t, k, [a, b, c]), r.value(t, k, [a, b, c]));
                if x.is_some() && y.is_some() && x != y {
                    return false;
                }
            }
        }
    }
    true
}

/// The gluing on every pair of the world's relations: the number of the
/// relation with its extent, if the world holds one.
pub fn table(query: &Query, rels: &[Ext]) -> Vec<Option<u32>> {
    let index: BTreeMap<&Ext, u32> = rels
        .iter()
        .enumerate()
        .map(|(i, e)| (e, i as u32))
        .collect();
    let k = rels.len();
    let mut table = vec![None; k * k];
    for r in 0..k {
        for s in 0..k {
            let e = query.eval(&[&rels[r], &rels[s]]);
            table[r * k + s] = index.get(&e).copied();
        }
    }
    table
}

/// Every gluing on worlds of relations, each with its number of points;
/// the first world proposes the coincidences (all expressions agree on
/// every triple of its relations), logic decides them, and the other
/// worlds are asked where logic does not give them.
pub fn explore(worlds: &[(usize, Vec<Ext>)]) -> Vec<Found> {
    let terms = Term::all();
    let mut out = Vec::new();
    for query in Query::gluings() {
        let mut tables = Vec::new();
        let mut total = Vec::new();
        for (n, rels) in worlds {
            let k = rels.len();
            let table = table(&query, rels);
            total.push((*n, table.iter().all(|t| t.is_some())));
            tables.push((*n, k, table));
        }
        let (_, k0, t0) = &tables[0];
        let mut classes: BTreeMap<Vec<Option<u32>>, Vec<usize>> = BTreeMap::new();
        for (i, term) in terms.iter().enumerate() {
            let mut sig = Vec::with_capacity(k0 * k0 * k0);
            for a in 0..*k0 as u32 {
                for b in 0..*k0 as u32 {
                    for c in 0..*k0 as u32 {
                        sig.push(term.value(t0, *k0, [a, b, c]));
                    }
                }
            }
            classes.entry(sig).or_default().push(i);
        }
        let mut seen = std::collections::BTreeSet::new();
        let mut laws = Vec::new();
        let mut members: Vec<Vec<usize>> = classes.into_values().filter(|c| c.len() > 1).collect();
        members.sort();
        for class in members {
            let rep = &terms[class[0]];
            for &m in &class[1..] {
                let (left, right) = canonical(rep, &terms[m]);
                if !seen.insert((left.clone(), right.clone())) {
                    continue;
                }
                let logic = by_logic(&left.query(&query), &right.query(&query));
                let worlds = tables
                    .iter()
                    .enumerate()
                    .map(|(w, (n, k, t))| {
                        let v = if w == 0 {
                            Some(true)
                        } else if logic.is_ok() {
                            None
                        } else {
                            Some(holds(t, *k, &left, &right))
                        };
                        (*n, v)
                    })
                    .collect();
                laws.push(Law {
                    left,
                    right,
                    logic,
                    worlds,
                });
            }
        }
        out.push(Found { query, total, laws });
    }
    out
}

/// The findings as a world for the kernel: what logic gives holds on every
/// plane; what a world shows holds on its plane; that a law seen on a world
/// holds is a defeasible rule; the frozen query of a law logic denies is a
/// world of its own where the law fails, strictly.
pub fn to_agl(found: &[Found]) -> String {
    let mut s =
        String::from("# Relations between relations (H75, stage A); made by agl --layer.\n");
    s += "axis world\n";
    let mut sizes: Vec<usize> = Vec::new();
    for f in found {
        sizes.extend(f.total.iter().map(|t| t.0));
        for l in &f.laws {
            if let Err(n) = l.logic {
                sizes.push(n);
            }
        }
    }
    sizes.sort();
    sizes.dedup();
    for n in &sizes {
        writeln!(s, "value world n{n}").unwrap();
    }
    s += "relation total(glue)\nrelation law(glue, law)\nrelation seen(glue, law, world)\n";
    s += "rule general defeasible @ : law(glue: ?g, law: ?l) <- seen(glue: ?g, law: ?l, world: ?w)\n";
    for (i, f) in found.iter().enumerate() {
        writeln!(s, "# g{i}: X∘Y = {}", f.query).unwrap();
        for (n, t) in &f.total {
            if *t {
                writeln!(s, "fact total_g{i}_n{n}: total(glue: g{i}) @ world:n{n}").unwrap();
            }
        }
        for (j, l) in f.laws.iter().enumerate() {
            let id = format!("g{i}_l{j}");
            let at = format!("glue: g{i}, law: l{j}");
            writeln!(s, "# {id}: {} = {}", l.left, l.right).unwrap();
            match l.logic {
                Ok(()) => {
                    writeln!(s, "fact {id}: law({at}) @").unwrap();
                    writeln!(s, "query law({at}) @ expect yes").unwrap();
                }
                Err(n) => {
                    writeln!(s, "fact {id}_frozen: ¬law({at}) @ world:n{n}").unwrap();
                    writeln!(s, "query law({at}) @ world:n{n} expect no").unwrap();
                }
            }
            for (n, v) in &l.worlds {
                match v {
                    Some(true) => {
                        writeln!(s, "fact {id}_n{n}: seen({at}, world: n{n}) @").unwrap();
                        writeln!(s, "query law({at}) @ world:n{n} expect yes").unwrap();
                    }
                    Some(false) => {
                        writeln!(s, "fact {id}_not_n{n}: ¬law({at}) @ world:n{n}").unwrap();
                        writeln!(s, "query law({at}) @ world:n{n} expect no").unwrap();
                    }
                    None => {}
                }
            }
        }
    }
    s
}

//! A concept as a pair (extent, intent) of exact bit vectors (H61, step 5a;
//! H68): the formal context of Wille (1982) over a whole ontology.
//!
//!     python3 tools/onto_stats.py fca chebi 244 target/scratch/fca244
//!     python3 tools/onto_stats.py fca chebi 255 target/scratch/fca255
//!     cargo run --release --example fca -- target/scratch/fca244 target/scratch/fca255
//!
//! Objects are the terms; attributes are the classes (a term has class G
//! when it is within G, G itself included) and the roles (a term has role R
//! when it or an ancestor has_role R or a species of R: step 4). The extent
//! of a class is its label region, unfolded into bits. A set of attributes
//! is compared with another two ways: by definition (each attribute of one
//! follows from the other's by the edges) and by extent (one extent within
//! the other). A proposal is an inclusion by extent that the edges do not
//! give. The second directory, if given, is a later release: how many
//! proposals hold there.

use agl::label::Labels;
use agl::sim::Rng;
use std::collections::{BTreeMap, BTreeSet};

const ROLE: &str = "CHEBI:50906";

/// (class, the class or role proposed for it)
type Pair<'a> = (&'a str, &'a str);

/// An exact bit vector over the objects, by postorder number.
#[derive(Clone, PartialEq, Eq)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Self {
        Bits(vec![0; n.div_ceil(64)])
    }
    fn full(n: usize) -> Self {
        let mut b = Bits(vec![u64::MAX; n.div_ceil(64)]);
        if !n.is_multiple_of(64) {
            *b.0.last_mut().expect("n > 0") = (1u64 << (n % 64)) - 1;
        }
        b
    }
    fn set(&mut self, i: u32) {
        self.0[i as usize / 64] |= 1 << (i % 64);
    }
    fn clear(&mut self, i: u32) {
        self.0[i as usize / 64] &= !(1 << (i % 64));
    }
    fn get(&self, i: u32) -> bool {
        self.0[i as usize / 64] >> (i % 64) & 1 == 1
    }
    fn and(&mut self, o: &Bits) {
        self.0.iter_mut().zip(&o.0).for_each(|(a, b)| *a &= b);
    }
    fn or(&mut self, o: &Bits) {
        self.0.iter_mut().zip(&o.0).for_each(|(a, b)| *a |= b);
    }
    /// `self & !o == 0`
    fn within(&self, o: &Bits) -> bool {
        self.0.iter().zip(&o.0).all(|(a, b)| a & !b == 0)
    }
    fn count(&self) -> u32 {
        self.0.iter().map(|w| w.count_ones()).sum()
    }
    fn first(&self) -> Option<u32> {
        self.0
            .iter()
            .enumerate()
            .find(|(_, w)| **w != 0)
            .map(|(i, w)| i as u32 * 64 + w.trailing_zeros())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Attr<'a> {
    Class(&'a str),
    Role(&'a str),
}

struct Context<'a> {
    labels: Labels,
    parents: BTreeMap<&'a str, Vec<&'a str>>,
    /// class -> roles it has_role directly
    has: BTreeMap<&'a str, Vec<&'a str>>,
    roles: Vec<&'a str>,
    role_ext: BTreeMap<&'a str, Bits>,
    /// postorder number -> term
    by_num: Vec<&'a str>,
}

fn read(path: &std::path::Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn pairs(text: &str) -> Vec<(&str, &str)> {
    text.lines()
        .map(|l| l.split_once('\t').expect("a<TAB>b"))
        .collect()
}

impl<'a> Context<'a> {
    fn new(edges: &[(&'a str, &'a str)], has_role: &[(&'a str, &'a str)]) -> Self {
        let labels = Labels::build(edges.iter().copied());
        let mut parents: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for &(a, b) in edges {
            parents.entry(a).or_default().push(b);
        }
        // Labels rank names the same way: sorted, distinct.
        let mut names: Vec<&str> = edges.iter().flat_map(|&(a, b)| [a, b]).collect();
        names.sort_unstable();
        names.dedup();
        let mut by_num = vec![""; labels.len()];
        for t in names {
            let i = labels.number(t).expect("a node") as usize;
            assert!(by_num[i].is_empty(), "a cycle: {t} shares a number");
            by_num[i] = t;
        }
        let mut has: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        let mut sources: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
        for &(s, r) in has_role {
            has.entry(s).or_default().push(r);
            sources.entry(r).or_default().push(s);
        }
        let mut cx = Context {
            labels,
            parents,
            has,
            roles: Vec::new(),
            role_ext: BTreeMap::new(),
            by_num,
        };
        cx.roles = cx
            .by_num
            .iter()
            .copied()
            .filter(|t| cx.labels.within(t, ROLE))
            .collect();
        cx.roles.sort_unstable();
        for &r in &cx.roles.clone() {
            let mut e = Bits::new(cx.by_num.len());
            for q in cx.labels.descendants(r) {
                for s in sources.get(q).into_iter().flatten() {
                    e.or(&cx.class_ext(s));
                }
            }
            cx.role_ext.insert(r, e);
        }
        cx
    }

    fn n(&self) -> usize {
        self.by_num.len()
    }

    fn class_ext(&self, g: &str) -> Bits {
        let mut e = Bits::new(self.n());
        for &(lo, hi) in self.labels.intervals(g).unwrap_or(&[]) {
            (lo..=hi).for_each(|i| e.set(i));
        }
        e
    }

    fn ext(&self, a: Attr) -> Bits {
        match a {
            Attr::Class(g) => self.class_ext(g),
            Attr::Role(r) => self.role_ext[r].clone(),
        }
    }

    /// B′: the objects with every attribute of B.
    fn extent(&self, b: &BTreeSet<Attr>) -> Bits {
        let mut e = Bits::full(self.n());
        b.iter().for_each(|&a| e.and(&self.ext(a)));
        e
    }

    /// Ancestors by the edges, `t` excluded.
    fn up(&self, t: &'a str) -> BTreeSet<&'a str> {
        let mut out = BTreeSet::new();
        let mut todo = vec![t];
        while let Some(x) = todo.pop() {
            for &p in self.parents.get(x).into_iter().flatten() {
                if out.insert(p) {
                    todo.push(p);
                }
            }
        }
        out
    }

    /// What follows from B by the edges: classes upwards, roles upwards,
    /// and the roles that the classes have.
    fn by_definition(&self, b: &BTreeSet<Attr<'a>>) -> BTreeSet<Attr<'a>> {
        let mut classes = BTreeSet::new();
        let mut roles = BTreeSet::new();
        for &a in b {
            match a {
                Attr::Class(g) => {
                    classes.insert(g);
                    classes.extend(self.up(g));
                }
                Attr::Role(r) => {
                    roles.insert(r);
                }
            }
        }
        for g in &classes {
            roles.extend(self.has.get(g).into_iter().flatten().copied());
        }
        for r in roles.clone() {
            roles.extend(self.up(r));
        }
        let mut out: BTreeSet<Attr> = classes.into_iter().map(Attr::Class).collect();
        out.extend(roles.into_iter().map(Attr::Role));
        out
    }

    /// A′: the attributes every object of A has; A not empty.
    fn intent(&self, a: &Bits) -> BTreeSet<Attr<'a>> {
        let o = self.by_num[a.first().expect("not empty") as usize];
        self.by_definition(&BTreeSet::from([Attr::Class(o)]))
            .into_iter()
            .filter(|&x| a.within(&self.ext(x)))
            .collect()
    }

    fn term(&self, names: &BTreeMap<&str, Vec<&'a str>>, name: &str) -> &'a str {
        match names.get(name).map(Vec::as_slice) {
            Some([t]) => t,
            other => panic!("{name}: {other:?}"),
        }
    }

    /// Proposals by extent, as `tools/onto_stats.py propose`: for a class
    /// with at least 3 species, the minimal classes and roles that hold all
    /// species and do not follow from the class by the edges.
    fn proposals(&self) -> (Vec<Pair<'a>>, Vec<Pair<'a>>) {
        let (mut within, mut role) = (Vec::new(), Vec::new());
        let mut classes: Vec<&str> = self.by_num.clone();
        classes.sort_unstable();
        for a in classes {
            let mut sp = self.class_ext(a);
            sp.clear(self.labels.number(a).expect("a node"));
            if sp.count() < 3 {
                continue;
            }
            let have = self.by_definition(&BTreeSet::from([Attr::Class(a)]));
            let common: BTreeSet<Attr> = self
                .intent(&sp)
                .into_iter()
                .filter(|x| !have.contains(x))
                .collect();
            let minimal = |x: &Attr| {
                !common.iter().any(|y| {
                    y != x
                        && match (x, y) {
                            (Attr::Class(p), Attr::Class(q)) | (Attr::Role(p), Attr::Role(q)) => {
                                self.labels.within(q, p)
                            }
                            _ => false,
                        }
                })
            };
            for x in common.iter().filter(|x| minimal(x)) {
                match *x {
                    Attr::Class(b) => within.push((a, b)),
                    Attr::Role(r) if !self.labels.within(a, ROLE) => role.push((a, r)),
                    Attr::Role(_) => {}
                }
            }
        }
        (within, role)
    }
}

fn show(b: &BTreeSet<Attr>, name: &BTreeMap<&str, &str>) -> String {
    let v: Vec<String> = b
        .iter()
        .map(|a| match a {
            Attr::Class(g) => name.get(g).unwrap_or(g).to_string(),
            Attr::Role(r) => format!("role {}", name.get(r).unwrap_or(r)),
        })
        .collect();
    v.join(" + ")
}

fn verdict(below: bool, above: bool) -> &'static str {
    match (below, above) {
        (true, true) => "same",
        (true, false) => "below",
        (false, true) => "above",
        (false, false) => "apart",
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let dir = std::path::Path::new(&args[0]);
    let (edges_t, roles_t, names_t) = (
        read(&dir.join("edges.tsv")),
        read(&dir.join("roles.tsv")),
        read(&dir.join("names.tsv")),
    );
    let (edges, has_role, named) = (pairs(&edges_t), pairs(&roles_t), pairs(&names_t));
    let cx = Context::new(&edges, &has_role);
    let name: BTreeMap<&str, &str> = named.iter().copied().collect();
    let mut by_name: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for &(id, n) in &named {
        by_name.entry(n).or_default().push(id);
    }
    println!(
        "{}: {} objects, {} classes with roles {}, {} has_role",
        dir.display(),
        cx.n(),
        cx.n(),
        cx.roles.len(),
        has_role.len()
    );

    // (a) Bits equal labels.
    let mut bad = 0;
    for &g in &cx.by_num {
        bad += usize::from(cx.class_ext(g).count() as usize != cx.labels.descendant_count(g));
    }
    let mut rng = Rng::new(1);
    let mut agree = 0;
    for _ in 0..100_000 {
        let (a, b) = (*rng.pick(&cx.by_num), *rng.pick(&cx.by_num));
        let bit = cx.class_ext(b).get(cx.labels.number(a).expect("a node"));
        agree += usize::from(bit == cx.labels.within(a, b));
    }
    println!("(a) counts differ for {bad} classes; within agrees on {agree} of 100000 pairs");

    // (b) Galois connection on attribute sets drawn from an object.
    let (mut ok, mut runs) = (0, 0);
    for _ in 0..200 {
        let o = *rng.pick(&cx.by_num);
        let all: Vec<Attr> = cx
            .by_definition(&BTreeSet::from([Attr::Class(o)]))
            .into_iter()
            .collect();
        let k = 1 + rng.below(3);
        let b: BTreeSet<Attr> = (0..k).map(|_| *rng.pick(&all)).collect();
        let e = cx.extent(&b);
        let b2 = cx.intent(&e);
        let e3 = cx.extent(&b2);
        let mut c = b.clone();
        c.insert(*rng.pick(&all));
        let fine = b.is_subset(&b2) && e3 == e && cx.extent(&c).within(&e);
        ok += usize::from(fine);
        runs += 1;
    }
    println!("(b) B ⊆ B″, B‴ = B′, more attributes give a smaller extent: {ok} of {runs}");

    // (c) Declared examples.
    let class = |n: &str| Attr::Class(cx.term(&by_name, n));
    let role = |n: &str| Attr::Role(cx.term(&by_name, n));
    let compare = |x: BTreeSet<Attr>, y: BTreeSet<Attr>, species: bool| {
        let (dx, dy) = (cx.by_definition(&x), cx.by_definition(&y));
        let (mut ex, ey) = (cx.extent(&x), cx.extent(&y));
        if species && let [Attr::Class(a)] = x.iter().copied().collect::<Vec<_>>()[..] {
            ex.clear(cx.labels.number(a).expect("a node"));
        }
        let by_def = verdict(y.is_subset(&dx), x.is_subset(&dy));
        let by_ext = verdict(ex.within(&ey), !species && ey.within(&ex));
        println!(
            "(c) {} vs {}: by definition {by_def}; by extent {by_ext} ({} and {} objects{})",
            show(&x, &name),
            show(&y, &name),
            ex.count(),
            ey.count(),
            if species { ", species only" } else { "" }
        );
    };
    compare(
        BTreeSet::from([class("aldose"), class("hexose")]),
        BTreeSet::from([class("aldohexose")]),
        false,
    );
    compare(
        BTreeSet::from([class("androstane ester")]),
        BTreeSet::from([class("steroid sulfate")]),
        true,
    );
    compare(
        BTreeSet::from([class("n-alkanal")]),
        BTreeSet::from([class("saturated fatty aldehyde")]),
        true,
    );
    let fa = BTreeSet::from([class("flavonoid"), role("antioxidant")]);
    let e = cx.extent(&fa);
    let b2 = cx.intent(&e);
    let more: BTreeSet<Attr> = b2.difference(&cx.by_definition(&fa)).copied().collect();
    println!(
        "(c) {}: {} objects; by extent they also share, beyond the definition: {}",
        show(&fa, &name),
        e.count(),
        if more.is_empty() {
            "nothing".to_string()
        } else {
            show(&more, &name)
        }
    );

    // (d) Proposals, and how many hold in a later release.
    let (within, role_p) = cx.proposals();
    let same = within
        .iter()
        .filter(|(a, b)| cx.labels.within(b, a))
        .count();
    println!(
        "(d) proposals: within {} ({same} of them a species holding all others), role {}",
        within.len(),
        role_p.len()
    );
    if let Some(next) = args.get(1) {
        let d = std::path::Path::new(next);
        let (e2, r2) = (read(&d.join("edges.tsv")), read(&d.join("roles.tsv")));
        let (e2, r2) = (pairs(&e2), pairs(&r2));
        let later = Context::new(&e2, &r2);
        let hold_w = within
            .iter()
            .filter(|(a, b)| later.labels.number(a).is_some() && later.labels.within(a, b))
            .count();
        let hold_r = role_p
            .iter()
            .filter(|&&(a, r)| {
                later.labels.number(a).is_some()
                    && later
                        .by_definition(&BTreeSet::from([Attr::Class(a)]))
                        .contains(&Attr::Role(r))
            })
            .count();
        println!("(d) hold in {next}: within {hold_w}, role {hold_r}");
    }
}

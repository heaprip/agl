//! Experiment E1, mechanism (external experiment, not the kernel).
//!
//! Input: a file of relation occurrences with ports and a source tag:
//!   occ <id> rel <R> port <P> -> <target> port <P> -> <target> src <S>
//! All labels are opaque. The mechanism is given nothing about what to
//! look for: it glues occurrences, finds condensations (two constructions
//! with one boundary), tests the "invariant" method for every candidate
//! (relation set, axis genus), lays projections against each other and
//! fixes what survives, with a control on random twins of every projection.
//!
//! Usage: e1_mechanism <input> [reverse]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::fs;
use std::process::exit;

const TWINS: u64 = 20;
const MAX_ELEMENTS: u64 = 1_000_000;
const MAX_STEPS: u64 = 2_000_000_000;

/// Counters instead of clocks: every created element and every step.
struct Budget {
    live: u64,
    steps: u64,
}

impl Budget {
    fn step(&mut self, n: u64) {
        self.steps += n;
        if self.steps > MAX_STEPS {
            println!("limit: steps above {MAX_STEPS}");
            exit(3);
        }
    }
    fn hold(&mut self, n: u64) {
        self.live += n;
        if self.live > MAX_ELEMENTS {
            println!("limit: live elements above {MAX_ELEMENTS}");
            exit(3);
        }
    }
    fn release(&mut self, n: u64) {
        self.live -= n;
    }
}

/// splitmix64; seeds come from the input hash only.
struct Rng(u64);

impl Rng {
    fn new(seed: u64, a: u64, b: u64) -> Rng {
        let mut r = Rng(seed
            ^ a.wrapping_mul(0x9E37_79B9_7F4A_7C15)
            ^ b.wrapping_mul(0xD1B5_4A32_D192_ED03));
        r.next();
        r
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        let zone = u64::MAX - u64::MAX % n;
        loop {
            let x = self.next();
            if x < zone {
                return x % n;
            }
        }
    }
}

/// An occurrence of a two-port relation. `a` is the target of the port
/// with the smaller label, `b` of the other: passing from `a` to `b` is
/// the step, from `b` to `a` its reversal.
#[derive(Clone, Copy)]
struct Occ {
    id: usize,
    rel: usize,
    a: usize,
    b: usize,
}

struct Input {
    names: Vec<String>,
    /// Occurrences per projection, projections in label order.
    projs: Vec<(usize, Vec<Occ>)>,
    rels: Vec<usize>,
    hash: u64,
    lines: usize,
    initial_axes: Vec<String>,
    skipped: Vec<String>,
}

fn fnv(bytes: &[u8], mut h: u64) -> u64 {
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x100_0000_01B3);
    }
    h
}

fn parse(path: &str) -> Input {
    let text = fs::read_to_string(path).unwrap_or_else(|e| {
        println!("input: {e}");
        exit(1)
    });
    let mut lines: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
    lines.sort();
    let mut hash = 0xCBF2_9CE4_8422_2325u64;
    for l in &lines {
        hash = fnv(l.as_bytes(), hash);
        hash = fnv(b"\n", hash);
    }
    if lines.len() as u64 > MAX_ELEMENTS {
        println!("limit: {} input lines", lines.len());
        exit(3);
    }
    // raw: (id, rel, [(port, target)], src)
    type Raw<'a> = (&'a str, &'a str, Vec<(&'a str, &'a str)>, &'a str);
    let mut raw: Vec<Raw> = Vec::new();
    let mut labels = BTreeSet::new();
    for l in &lines {
        let t: Vec<&str> = l.split_whitespace().collect();
        let bad = || -> ! {
            println!("input: malformed line: {l}");
            exit(1)
        };
        if t.len() < 6 || t[0] != "occ" || t[2] != "rel" || t[t.len() - 2] != "src" {
            bad();
        }
        let mut ports = Vec::new();
        let mut i = 4;
        while i + 1 < t.len() - 2 {
            if t[i] != "port" || t[i + 2] != "->" || i + 3 >= t.len() - 2 {
                bad();
            }
            ports.push((t[i + 1], t[i + 3]));
            i += 4;
        }
        if i != t.len() - 2 {
            bad();
        }
        for x in [t[1], t[3], t[t.len() - 1]] {
            labels.insert(x);
        }
        for &(p, x) in &ports {
            labels.insert(p);
            labels.insert(x);
        }
        raw.push((t[1], t[3], ports, t[t.len() - 1]));
    }
    let names: Vec<String> = labels.iter().map(|s| s.to_string()).collect();
    let ix = |s: &str| names.binary_search_by(|n| n.as_str().cmp(s)).unwrap();
    // ports of each relation, and targets of each (relation, port)
    let mut rel_ports: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
    let mut port_targets: BTreeMap<(usize, usize), BTreeSet<usize>> = BTreeMap::new();
    for (_, r, ports, _) in &raw {
        for &(p, x) in ports {
            rel_ports.entry(ix(r)).or_default().insert(ix(p));
            port_targets
                .entry((ix(r), ix(p)))
                .or_default()
                .insert(ix(x));
        }
    }
    let mut skipped = Vec::new();
    let mut rels = Vec::new();
    for (&r, ps) in &rel_ports {
        if ps.len() == 2 {
            rels.push(r);
        } else {
            skipped.push(format!(
                "relation {} has {} ports: not handled (gap)",
                names[r],
                ps.len()
            ));
        }
    }
    // First axes from the form of the data: a port whose targets never
    // appear as targets of any other port gives an axis without order.
    let mut initial_axes = Vec::new();
    for (&(r, p), xs) in &port_targets {
        let elsewhere = port_targets
            .iter()
            .filter(|(k, _)| **k != (r, p))
            .any(|(_, ys)| !xs.is_disjoint(ys));
        if !elsewhere && rel_ports[&r].len() == 2 {
            let other = *rel_ports[&r].iter().find(|&&q| q != p).unwrap();
            initial_axes.push(format!(
                "initial axis unordered: relation {} port {} positioned by port {} values {}",
                names[r],
                names[other],
                names[p],
                xs.len()
            ));
        }
    }
    let mut by_src: BTreeMap<usize, Vec<Occ>> = BTreeMap::new();
    for (id, r, ports, s) in &raw {
        let r = ix(r);
        if !rels.contains(&r) {
            continue;
        }
        let mut ps: Vec<(usize, usize)> = ports.iter().map(|&(p, x)| (ix(p), ix(x))).collect();
        ps.sort();
        if ps.len() != 2 || ps[0].0 == ps[1].0 {
            println!("input: occurrence {id} does not fill both ports once");
            exit(1);
        }
        by_src.entry(ix(s)).or_default().push(Occ {
            id: ix(id),
            rel: r,
            a: ps[0].1,
            b: ps[1].1,
        });
    }
    Input {
        names,
        projs: by_src.into_iter().collect(),
        rels,
        hash,
        lines: lines.len(),
        initial_axes,
        skipped,
    }
}

/// A condensation: closing occurrence `occ` passed from `x` to `y` in
/// direction `dir`, against the tree path from `x` to `y`. `c` is the
/// net count per relation slot around the cycle (closing, then back).
struct Cond {
    occ: usize,
    dir: i64,
    x: usize,
    y: usize,
    c: [i64; 2],
}

/// Gluing of a candidate's occurrences in one projection: breadth-first
/// from the smallest label of every connected part; potentials are net
/// counts per slot along the tree from the part's start.
struct Glue {
    ents: Vec<usize>,
    pot: Vec<[i64; 2]>,
    tree_in: Vec<Option<(usize, i64, usize)>>,
    adj: Vec<Vec<(usize, usize, i64)>>,
    conds: Vec<Cond>,
    occs: Vec<(usize, Occ)>,
}

fn glue(occs: &[Occ], set: &[usize], budget: &mut Budget) -> Glue {
    let sel: Vec<(usize, Occ)> = occs
        .iter()
        .filter_map(|o| set.iter().position(|&r| r == o.rel).map(|s| (s, *o)))
        .collect();
    let mut ents: Vec<usize> = sel.iter().flat_map(|(_, o)| [o.a, o.b]).collect();
    ents.sort();
    ents.dedup();
    let n = ents.len();
    let at = |x: usize| ents.binary_search(&x).unwrap();
    let mut adj: Vec<Vec<(usize, usize, i64)>> = vec![Vec::new(); n];
    let mut loops = Vec::new();
    for (e, (_, o)) in sel.iter().enumerate() {
        let (u, v) = (at(o.a), at(o.b));
        if u == v {
            loops.push((e, u));
        } else {
            adj[u].push((e, v, 1));
            adj[v].push((e, u, -1));
        }
    }
    budget.step((sel.len() + n) as u64);
    let unit = |s: usize, d: i64| if s == 0 { [d, 0] } else { [0, d] };
    let mut seen = vec![false; n];
    let mut used = vec![false; sel.len()];
    let mut pot = vec![[0i64; 2]; n];
    let mut tree_in = vec![None; n];
    let mut conds = Vec::new();
    for root in 0..n {
        if seen[root] {
            continue;
        }
        seen[root] = true;
        let mut q = VecDeque::from([root]);
        while let Some(x) = q.pop_front() {
            for &(e, y, d) in &adj[x] {
                budget.step(1);
                if used[e] {
                    continue;
                }
                used[e] = true;
                let s = unit(sel[e].0, d);
                if !seen[y] {
                    seen[y] = true;
                    pot[y] = [pot[x][0] + s[0], pot[x][1] + s[1]];
                    tree_in[y] = Some((e, d, x));
                    q.push_back(y);
                } else {
                    conds.push(Cond {
                        occ: e,
                        dir: d,
                        x,
                        y,
                        c: [s[0] + pot[x][0] - pot[y][0], s[1] + pot[x][1] - pot[y][1]],
                    });
                }
            }
        }
    }
    // An occurrence with both ports on one target: the occurrence against
    // its own reversal (two non-empty constructions, one boundary).
    for (e, u) in loops {
        let s = unit(sel[e].0, 2);
        conds.push(Cond {
            occ: e,
            dir: 1,
            x: u,
            y: u,
            c: s,
        });
    }
    budget.hold(conds.len() as u64);
    Glue {
        ents,
        pot,
        tree_in,
        adj,
        conds,
        occs: sel,
    }
}

impl Glue {
    /// The cycle of a condensation as (occurrence id, direction) items.
    fn cycle(&self, k: &Cond) -> Vec<(usize, i64)> {
        let mut out = vec![(self.occs[k.occ].1.id, k.dir)];
        if k.x == k.y {
            return out;
        }
        let depth = |mut v: usize| {
            let mut d = 0;
            while let Some((_, _, p)) = self.tree_in[v] {
                v = p;
                d += 1;
            }
            d
        };
        let (mut u, mut v) = (k.y, k.x);
        let (mut du, mut dv) = (depth(u), depth(v));
        let mut up = Vec::new(); // from y upwards, passed against tree direction
        let mut down = Vec::new(); // from x upwards, later reversed
        while du > dv {
            let (e, d, p) = self.tree_in[u].unwrap();
            up.push((self.occs[e].1.id, -d));
            u = p;
            du -= 1;
        }
        while dv > du {
            let (e, d, p) = self.tree_in[v].unwrap();
            down.push((self.occs[e].1.id, d));
            v = p;
            dv -= 1;
        }
        while u != v {
            let (e, d, p) = self.tree_in[u].unwrap();
            up.push((self.occs[e].1.id, -d));
            u = p;
            let (e, d, p) = self.tree_in[v].unwrap();
            down.push((self.occs[e].1.id, d));
            v = p;
        }
        down.reverse();
        out.extend(up);
        out.extend(down);
        out
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Genus {
    Shift,
    Laws,
    Equal,
}

impl Genus {
    fn name(self) -> &'static str {
        match self {
            Genus::Shift => "shift",
            Genus::Laws => "laws",
            Genus::Equal => "equal",
        }
    }
}

/// Plane of solutions of one candidate (step space of its relations).
#[derive(Clone, PartialEq, Eq, Debug)]
enum Plane {
    /// every step free (dimension = number of relations)
    Full,
    /// one-dimensional, one of these primitive directions (a fork if >1)
    Dirs(Vec<[i64; 2]>),
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.abs() } else { gcd(b, a % b) }
}

/// Fewest violated condensations over non-degenerate planes (every step of
/// the set non-zero; the relation itself is the unit).
fn solve(g: &Glue, size: usize, genus: Genus) -> (usize, Plane) {
    if genus != Genus::Shift {
        // all steps equal satisfies every condensation of two non-empty
        // constructions
        return (0, Plane::Full);
    }
    let nonzero: Vec<[i64; 2]> = g
        .conds
        .iter()
        .map(|k| k.c)
        .filter(|c| *c != [0, 0])
        .collect();
    if size == 1 {
        return (nonzero.len(), Plane::Full);
    }
    let mut tally: BTreeMap<[i64; 2], usize> = BTreeMap::new();
    for c in &nonzero {
        if c[0] != 0 && c[1] != 0 {
            let k = gcd(c[0], c[1]);
            let mut d = [c[1] / k, -c[0] / k];
            if d[0] < 0 {
                d = [-d[0], -d[1]];
            }
            *tally.entry(d).or_default() += 1;
        }
    }
    let best = tally.values().copied().max().unwrap_or(0);
    if best == 0 {
        return (nonzero.len(), Plane::Full);
    }
    let dirs = tally
        .iter()
        .filter(|(_, n)| **n == best)
        .map(|(d, _)| *d)
        .collect();
    (nonzero.len() - best, Plane::Dirs(dirs))
}

fn meet(p: &Plane, q: &Plane) -> Option<Plane> {
    match (p, q) {
        (Plane::Full, x) | (x, Plane::Full) => Some(x.clone()),
        (Plane::Dirs(a), Plane::Dirs(b)) => {
            let c: Vec<[i64; 2]> = a.iter().filter(|d| b.contains(d)).copied().collect();
            if c.is_empty() {
                None
            } else {
                Some(Plane::Dirs(c))
            }
        }
    }
}

fn holds(c: [i64; 2], plane: &Plane, size: usize) -> bool {
    match plane {
        Plane::Full => c == [0, 0] || (size == 1 && c[0] == 0),
        Plane::Dirs(ds) => ds.iter().all(|d| c[0] * d[0] + c[1] * d[1] == 0),
    }
}

#[derive(Clone, Debug)]
enum State {
    Empty,
    Strict,
    Exceptions { v: usize, twin_min: usize },
    Refuted { v: usize, twin_min: usize },
}

struct Verdict {
    states: Vec<State>,
    plane: Option<Plane>,
    nonempty: usize,
    status: String,
    fixed: Option<bool>,
}

/// Twin of a projection: same occurrences, relations and ports; every port
/// target drawn from the projection's targets.
fn twin(occs: &[Occ], hash: u64, proj: usize, j: u64) -> Vec<Occ> {
    let pool: Vec<usize> = occs
        .iter()
        .flat_map(|o| [o.a, o.b])
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let mut rng = Rng::new(hash, proj as u64 + 1, j + 1);
    let n = pool.len() as u64;
    occs.iter()
        .map(|o| {
            let a = pool[rng.below(n) as usize];
            let b = pool[rng.below(n) as usize];
            Occ { a, b, ..*o }
        })
        .collect()
}

#[allow(clippy::needless_range_loop)] // j indexes twin worlds across projections
fn fit(
    projs: &[(usize, Vec<Occ>)],
    twins: &[Vec<Vec<Occ>>],
    set: &[usize],
    genus: Genus,
    budget: &mut Budget,
) -> Verdict {
    let mut states = Vec::new();
    let mut plane = Some(Plane::Full);
    let mut nonempty = 0;
    let mut refuted_any = false;
    for (p, (_, occs)) in projs.iter().enumerate() {
        let g = glue(occs, set, budget);
        let (v, pl) = solve(&g, set.len(), genus);
        let st = if g.conds.is_empty() {
            State::Empty
        } else if v == 0 {
            State::Strict
        } else {
            let mut twin_min = usize::MAX;
            for t in &twins[p] {
                let tg = glue(t, set, budget);
                twin_min = twin_min.min(solve(&tg, set.len(), genus).0);
                budget.release(tg.conds.len() as u64);
            }
            if v < twin_min {
                State::Exceptions { v, twin_min }
            } else {
                State::Refuted { v, twin_min }
            }
        };
        budget.release(g.conds.len() as u64);
        match st {
            State::Empty => {}
            State::Refuted { .. } => {
                nonempty += 1;
                refuted_any = true;
            }
            _ => {
                nonempty += 1;
                plane = plane.and_then(|q| meet(&q, &pl));
            }
        }
        states.push(st);
    }
    let mut fixed = None;
    let status = if refuted_any {
        "not fitted: refuted in a projection".to_string()
    } else if nonempty == 0 {
        "not fitted: empty in every projection".to_string()
    } else if nonempty == 1 {
        "not fitted: holds in one projection, no second projection".to_string()
    } else if plane.is_none() {
        "not fitted: planes of projections do not meet".to_string()
    } else {
        // control of form: strict fit on some twin world
        let mut form = None;
        for j in 0..TWINS as usize {
            let mut tplane = Some(Plane::Full);
            let mut tn = 0;
            let mut bad = false;
            for (p, _) in projs.iter().enumerate() {
                let tg = glue(&twins[p][j], set, budget);
                let (v, pl) = solve(&tg, set.len(), genus);
                budget.release(tg.conds.len() as u64);
                if tg.conds.is_empty() {
                    continue;
                }
                tn += 1;
                if v > 0 {
                    bad = true;
                    break;
                }
                tplane = tplane.and_then(|q| meet(&q, &pl));
            }
            if !bad && tn >= 2 && tplane.is_some() {
                form = Some(j + 1);
                break;
            }
        }
        match form {
            Some(j) => format!("law of form: fits strictly on twin world {j}"),
            None => {
                let defeasible = states.iter().any(|s| matches!(s, State::Exceptions { .. }));
                fixed = Some(defeasible);
                format!(
                    "fixed {}; fits on no twin world of {TWINS}",
                    if defeasible { "defeasible" } else { "strict" }
                )
            }
        }
    };
    Verdict {
        states,
        plane,
        nonempty,
        status,
        fixed,
    }
}

fn dims(plane: &Plane, size: usize) -> usize {
    match plane {
        Plane::Full => size,
        Plane::Dirs(_) => 1,
    }
}

/// Basis of the fixed plane: step vectors over the relation slots.
fn basis(plane: &Plane, size: usize) -> Vec<Vec<[i64; 2]>> {
    match plane {
        Plane::Full if size == 1 => vec![vec![[1, 0]]],
        Plane::Full => vec![vec![[1, 0], [0, 1]]],
        Plane::Dirs(ds) => ds.iter().map(|d| vec![*d]).collect(),
    }
}

fn dot(a: [i64; 2], b: [i64; 2]) -> i64 {
    a[0] * b[0] + a[1] * b[1]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 || args.len() > 3 || (args.len() == 3 && args[2] != "reverse") {
        println!("usage: e1_mechanism <input> [reverse]");
        exit(1);
    }
    let reverse = args.len() == 3;
    let mut budget = Budget { live: 0, steps: 0 };
    let inp = parse(&args[1]);
    let nm = |x: usize| inp.names[x].as_str();
    let mut out = String::new();
    let total_occ: usize = inp.projs.iter().map(|(_, o)| o.len()).sum();
    budget.hold(total_occ as u64);
    let _ = writeln!(out, "e1 mechanism report");
    let _ = writeln!(
        out,
        "input hash {:016x} lines {} projections {} relations {}",
        inp.hash,
        inp.lines,
        inp.projs.len(),
        inp.rels.len()
    );
    for s in &inp.skipped {
        let _ = writeln!(out, "{s}");
    }
    // size estimate before gluing
    let mut ents_total = 0;
    let mut rank_total: i64 = 0;
    for (_, occs) in &inp.projs {
        let g = glue(occs, &inp.rels, &mut budget);
        ents_total += g.ents.len();
        rank_total += g.conds.len() as i64;
        budget.release(g.conds.len() as u64);
    }
    let _ = writeln!(
        out,
        "estimate entities {ents_total} occurrences {total_occ} condensations {rank_total} twins per projection {TWINS}"
    );
    let _ = writeln!(out, "-- initial axes");
    for a in &inp.initial_axes {
        let _ = writeln!(out, "{a}");
    }
    // twins of every projection, from the input hash
    let twins: Vec<Vec<Vec<Occ>>> = inp
        .projs
        .iter()
        .enumerate()
        .map(|(p, (_, occs))| {
            budget.hold(occs.len() as u64 * TWINS);
            (0..TWINS).map(|j| twin(occs, inp.hash, p, j)).collect()
        })
        .collect();
    // candidate relation sets: single relations; pairs with common
    // condensations
    let rank = |set: &[usize], budget: &mut Budget| -> Vec<usize> {
        inp.projs
            .iter()
            .map(|(_, occs)| {
                let g = glue(occs, set, budget);
                budget.release(g.conds.len() as u64);
                g.conds.len()
            })
            .collect()
    };
    let mut sets: Vec<(Vec<usize>, usize)> = Vec::new();
    let singles: Vec<Vec<usize>> = inp.rels.iter().map(|&r| rank(&[r], &mut budget)).collect();
    for (i, &r) in inp.rels.iter().enumerate() {
        sets.push((vec![r], singles[i].iter().sum()));
    }
    for i in 0..inp.rels.len() {
        for j in i + 1..inp.rels.len() {
            let pr = rank(&[inp.rels[i], inp.rels[j]], &mut budget);
            let common = (0..inp.projs.len()).any(|p| pr[p] > singles[i][p] + singles[j][p]);
            if common {
                sets.push((vec![inp.rels[i], inp.rels[j]], pr.iter().sum()));
            }
        }
    }
    let mut cands: Vec<(usize, Genus, Vec<usize>)> = Vec::new();
    for (set, score) in &sets {
        for g in [Genus::Shift, Genus::Laws, Genus::Equal] {
            cands.push((*score, g, set.clone()));
        }
    }
    cands.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)).then(a.2.cmp(&b.2)));
    if reverse {
        cands.reverse();
    }
    let label = |set: &[usize]| set.iter().map(|&r| nm(r)).collect::<Vec<_>>().join(",");
    let _ = writeln!(
        out,
        "-- candidates (order: fruitfulness = condensations, {})",
        if reverse { "reversed" } else { "most first" }
    );
    let mut fixed: BTreeMap<(Genus, Vec<usize>), (Verdict, usize)> = BTreeMap::new();
    let mut anomalies = Vec::new();
    for (score, genus, set) in &cands {
        let v = fit(&inp.projs, &twins, set, *genus, &mut budget);
        let (mut e, mut s, mut x, mut r) = (0, 0, 0, 0);
        for st in &v.states {
            match st {
                State::Empty => e += 1,
                State::Strict => s += 1,
                State::Exceptions { .. } => x += 1,
                State::Refuted { .. } => r += 1,
            }
        }
        let _ = writeln!(
            out,
            "cand {} rels {} condensations {score}: projections empty {e} strict {s} exceptions {x} refuted {r}; {}",
            genus.name(),
            label(set),
            v.status
        );
        if *genus == Genus::Shift && set.len() == 1 {
            for (p, st) in v.states.iter().enumerate() {
                if let State::Refuted { v: n, twin_min } = st {
                    let g = glue(&inp.projs[p].1, set, &mut budget);
                    let mut shown = 0;
                    for k in &g.conds {
                        if k.c == [0, 0] || shown == 3 {
                            continue;
                        }
                        shown += 1;
                        let cyc = g.cycle(k);
                        let fwd = cyc.iter().filter(|c| c.1 > 0).count();
                        let back = cyc.len() - fwd;
                        anomalies.push(format!(
                            "anomaly shift rels {} src {}: closed path with net step {} (forward {fwd} backward {back}) at closing {}; violated {n} of {}, twin minimum {twin_min}",
                            label(set),
                            nm(inp.projs[p].0),
                            k.c[0],
                            nm(g.occs[k.occ].1.id),
                            g.conds.len()
                        ));
                    }
                    budget.release(g.conds.len() as u64);
                }
            }
        }
        if v.fixed.is_some() {
            fixed.insert((*genus, set.clone()), (v, *score));
        }
    }
    let _ = writeln!(out, "-- anomalies");
    for a in &anomalies {
        let _ = writeln!(out, "{a}");
    }
    let _ = writeln!(out, "-- fixed");
    let mut n_shift_axes = 0;
    for ((genus, set), (v, score)) in &fixed {
        let plane = v.plane.clone().unwrap();
        let d = dims(&plane, set.len());
        if *genus == Genus::Shift {
            n_shift_axes += d;
        }
        let _ = writeln!(
            out,
            "fixed {} rels {} dim {} {}",
            genus.name(),
            label(set),
            d,
            if v.fixed == Some(true) {
                "defeasible"
            } else {
                "strict"
            }
        );
        let _ = writeln!(
            out,
            "  support projections {} of {}; condensations {score}",
            v.nonempty,
            inp.projs.len()
        );
        for (p, st) in v.states.iter().enumerate() {
            let s = match st {
                State::Empty => "empty".to_string(),
                State::Strict => "strict".to_string(),
                State::Exceptions { v, twin_min } => {
                    format!("exceptions {v}, fewer than every twin (minimum {twin_min})")
                }
                State::Refuted { v, twin_min } => format!("refuted {v} (twin minimum {twin_min})"),
            };
            let _ = writeln!(out, "  projection {} {s}", nm(inp.projs[p].0));
        }
        match &plane {
            Plane::Full => {
                let _ = writeln!(out, "  plane: every step free, relation is the unit");
            }
            Plane::Dirs(ds) => {
                let s: Vec<String> = ds.iter().map(|d| format!("({},{})", d[0], d[1])).collect();
                let _ = writeln!(
                    out,
                    "  plane: direction{} {}",
                    if ds.len() > 1 { "s (fork)" } else { "" },
                    s.join(" ")
                );
            }
        }
        if *genus != Genus::Shift {
            continue;
        }
        let bases = basis(&plane, set.len());
        let (mut p2, mut o2, mut p3, mut o3) = (0u64, 0u64, 0u64, 0u64);
        for (p, (src, occs)) in inp.projs.iter().enumerate() {
            let g = glue(occs, set, &mut budget);
            let mut closing_bad = vec![false; g.occs.len()];
            for k in &g.conds {
                let ok = holds(k.c, &plane, set.len());
                let cyc = g.cycle(k);
                let items: Vec<String> = cyc
                    .iter()
                    .map(|(id, d)| format!("{}{}", nm(*id), if *d > 0 { "+" } else { "-" }))
                    .collect();
                let _ = writeln!(
                    out,
                    "  cond {} {} {}",
                    nm(*src),
                    if ok { "ok" } else { "refuted" },
                    items.join(" ")
                );
                if !ok {
                    closing_bad[k.occ] = true;
                    for b in &bases {
                        for s in b {
                            let via = dot(g.pot[k.x], *s) + k.dir * dot(unit_of(&g, k.occ), *s);
                            let _ = writeln!(
                                out,
                                "  exception {} closing {} fork entity {} positions {} {}",
                                nm(*src),
                                nm(g.occs[k.occ].1.id),
                                nm(g.ents[k.y]),
                                dot(g.pot[k.y], *s),
                                via
                            );
                        }
                    }
                }
            }
            // chains of 2 and 3 occurrences outside exceptions
            for start in 0..g.ents.len() {
                let mut stack: Vec<(usize, usize, [i64; 2])> = vec![(start, 0, [0, 0])];
                while let Some((x, len, acc)) = stack.pop() {
                    budget.step(1);
                    if len >= 2 {
                        let ok = bases.iter().all(|b| {
                            b.iter()
                                .all(|s| dot(g.pot[x], *s) - dot(g.pot[start], *s) == dot(acc, *s))
                        });
                        if len == 2 {
                            p2 += 1;
                            o2 += ok as u64;
                        } else {
                            p3 += 1;
                            o3 += ok as u64;
                        }
                    }
                    if len == 3 {
                        continue;
                    }
                    for &(e, y, d) in &g.adj[x] {
                        if closing_bad[e] {
                            continue;
                        }
                        let u = unit_of(&g, e);
                        stack.push((y, len + 1, [acc[0] + d * u[0], acc[1] + d * u[1]]));
                    }
                }
            }
            // occasion: step undefined at an edge of the axis
            let mut has_in = vec![false; g.ents.len()];
            let mut has_out = vec![false; g.ents.len()];
            for (_, o) in &g.occs {
                has_out[g.ents.binary_search(&o.a).unwrap()] = true;
                has_in[g.ents.binary_search(&o.b).unwrap()] = true;
            }
            let ni = has_in.iter().filter(|x| !**x).count();
            let no = has_out.iter().filter(|x| !**x).count();
            if !g.conds.is_empty() {
                let _ = writeln!(
                    out,
                    "  occasion {} reversed step undefined at {ni} entities, step undefined at {no}; extension: {} new positions beyond the edges, existing positions unchanged",
                    nm(*src),
                    ni + no
                );
            }
            budget.release(g.conds.len() as u64);
            let _ = p;
        }
        let _ = writeln!(out, "  pathcheck len2 {p2} {o2} len3 {p3} {o3}");
    }
    let _ = writeln!(out, "-- summary");
    let _ = writeln!(
        out,
        "summary fixed {} shift axes {n_shift_axes} anomalies {}",
        fixed.len(),
        anomalies.len()
    );
    let _ = writeln!(
        out,
        "provenance input hash {:016x}; twins seeded from the input hash; steps {}",
        inp.hash, budget.steps
    );
    print!("{out}");
}

fn unit_of(g: &Glue, e: usize) -> [i64; 2] {
    if g.occs[e].0 == 0 { [1, 0] } else { [0, 1] }
}

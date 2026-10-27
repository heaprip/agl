//! Experiment E1, world generator (external experiment, not the kernel).
//!
//! Writes worlds of families, rings and lattices as occurrence files for
//! `e1_mechanism`, with a journal that only the outside check reads. The
//! mechanism never sees this code, its names or its journal.
//!
//! Usage:
//!   e1_world gen <families|rings|lattice> <plain|shuffled|twin> <seed> <n> <label_seed> <out_prefix>
//!   e1_world permute <in> <seed> <out>
//!   e1_world check <journal> <report>

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::process::exit;

const MAX_PER_FAMILY: usize = 2000;
const MAX_OCCURRENCES: usize = 1_000_000;

/// splitmix64: all randomness of the generator comes from explicit seeds.
struct Rng(u64);

impl Rng {
    fn new(seed: u64, stream: u64) -> Rng {
        let mut r = Rng(seed ^ stream.wrapping_mul(0xA076_1D64_78BD_642F));
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
    /// Uniform in 0..n, by rejection.
    fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let zone = u64::MAX - u64::MAX % n;
        loop {
            let x = self.next();
            if x < zone {
                return x % n;
            }
        }
    }
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.below(i as u64 + 1) as usize;
            v.swap(i, j);
        }
    }
}

/// Opaque labels: every name in the output file is drawn from the label
/// seed, so labels change from seed to seed and carry no meaning.
struct Labels {
    rng: Rng,
    used: BTreeSet<String>,
}

impl Labels {
    fn new(seed: u64) -> Labels {
        Labels {
            rng: Rng::new(seed, 0x1AB),
            used: BTreeSet::new(),
        }
    }
    fn fresh(&mut self) -> String {
        loop {
            let s = format!("x{:08x}", self.rng.next() as u32);
            if self.used.insert(s.clone()) {
                return s;
            }
        }
    }
}

/// One occurrence in world terms: relation index, two (port index, target).
#[derive(Clone)]
struct Occ {
    rel: usize,
    ports: [(usize, usize); 2],
    src: usize,
    /// Journal only: for a parent occurrence, level(parent) - level(primary).
    bad_offset: i64,
}

struct World {
    /// Names of relations and of their two ports (journal only).
    rel_names: Vec<&'static str>,
    port_names: Vec<&'static str>,
    /// Number of targets; targets are 0..n_targets.
    n_targets: usize,
    occs: Vec<Occ>,
    n_src: usize,
    journal: Vec<String>,
}

fn families(seed: u64, n_fam: usize) -> World {
    // relations: 0 = parent (ports 0 parent-side, 1 child-side),
    //            1 = sex (ports 2 who, 3 value); targets 0,1 = sex values.
    let mut run = Rng::new(seed, 1);
    let q_per_mille = [50u64, 100, 200][run.below(3) as usize];
    let mut journal = vec![format!("q_per_mille {q_per_mille}")];
    let mut occs = Vec::new();
    let mut next_target = 2usize;
    for f in 0..n_fam {
        let mut rng = Rng::new(seed, 100 + f as u64);
        let depth = 2 + rng.below(5) as u32;
        // person: (global target, level, sex, member)
        let mut people: Vec<(usize, u32, u8, bool)> = Vec::new();
        let mut add = |people: &mut Vec<(usize, u32, u8, bool)>, level, sex, member| {
            people.push((next_target, level, sex, member));
            next_target += 1;
            people.len() - 1
        };
        let s0 = rng.below(2) as u8;
        let a = add(&mut people, 0, s0, true);
        let b = add(&mut people, 0, 1 - s0, true);
        let mut couples: VecDeque<(usize, usize)> = VecDeque::new();
        couples.push_back((a, b));
        let mut truncated = false;
        let mut cross = 0usize;
        let mut cross_with_children = 0usize;
        let mut par: Vec<(usize, usize, i64)> = Vec::new();
        'outer: while let Some((primary, partner)) = couples.pop_front() {
            let k = rng.below(4);
            let offset = people[partner].1 as i64 - people[primary].1 as i64;
            if offset != 0 && k > 0 && people[partner].3 && primary != a {
                cross_with_children += 1;
            }
            for _ in 0..k {
                if people.len() + 2 > MAX_PER_FAMILY {
                    truncated = true;
                    break 'outer;
                }
                let level = people[primary].1 + 1;
                let sex = rng.below(2) as u8;
                let kid = add(&mut people, level, sex, true);
                par.push((primary, kid, 0));
                par.push((partner, kid, offset));
                if level < depth {
                    let mut chosen = None;
                    if rng.below(1000) < q_per_mille {
                        let cand: Vec<usize> = (0..people.len())
                            .filter(|&i| i != kid && people[i].3 && people[i].2 != sex)
                            .collect();
                        if !cand.is_empty() {
                            let r = cand[rng.below(cand.len() as u64) as usize];
                            if people[r].1 != level {
                                cross += 1;
                            }
                            journal.push(format!(
                                "relative-marriage src {f} level {level} {}",
                                people[r].1
                            ));
                            chosen = Some(r);
                        }
                    }
                    let partner = match chosen {
                        Some(r) => r,
                        None => add(&mut people, level, 1 - sex, false),
                    };
                    couples.push_back((kid, partner));
                }
            }
        }
        journal.push(format!(
            "family src {f} depth {depth} persons {} truncated {truncated} crossgen_marriages {cross} crossgen_with_children {cross_with_children}",
            people.len()
        ));
        for &(p, c, off) in &par {
            occs.push(Occ {
                rel: 0,
                ports: [(0, people[p].0), (1, people[c].0)],
                src: f,
                bad_offset: off,
            });
        }
        for p in &people {
            occs.push(Occ {
                rel: 1,
                ports: [(2, p.0), (3, p.2 as usize)],
                src: f,
                bad_offset: 0,
            });
        }
    }
    World {
        rel_names: vec!["parent", "sex"],
        port_names: vec!["parent", "child", "who", "value"],
        n_targets: next_target,
        occs,
        n_src: n_fam,
        journal,
    }
}

fn rings(seed: u64, n: usize) -> World {
    let mut rng = Rng::new(seed, 2);
    let mut occs = Vec::new();
    let mut next = 0usize;
    let mut journal = Vec::new();
    for r in 0..n {
        let len = 3 + rng.below(7) as usize;
        journal.push(format!("ring src {r} length {len}"));
        for i in 0..len {
            occs.push(Occ {
                rel: 0,
                ports: [(0, next + i), (1, next + (i + 1) % len)],
                src: r,
                bad_offset: 0,
            });
        }
        next += len;
    }
    World {
        rel_names: vec!["next"],
        port_names: vec!["from", "to"],
        n_targets: next,
        occs,
        n_src: n,
        journal,
    }
}

fn lattice(seed: u64, n: usize) -> World {
    let mut rng = Rng::new(seed, 3);
    let mut occs = Vec::new();
    let mut next = 0usize;
    let mut journal = Vec::new();
    for l in 0..n {
        let a = 2 + rng.below(5) as usize;
        let b = 2 + rng.below(5) as usize;
        journal.push(format!("lattice src {l} size {a} {b}"));
        let id = |x: usize, y: usize| next + y * a + x;
        for y in 0..b {
            for x in 0..a {
                if x + 1 < a {
                    occs.push(Occ {
                        rel: 0,
                        ports: [(0, id(x, y)), (1, id(x + 1, y))],
                        src: l,
                        bad_offset: 0,
                    });
                }
                if y + 1 < b {
                    occs.push(Occ {
                        rel: 1,
                        ports: [(2, id(x, y)), (3, id(x, y + 1))],
                        src: l,
                        bad_offset: 0,
                    });
                }
            }
        }
        next += a * b;
    }
    World {
        rel_names: vec!["right", "up"],
        port_names: vec!["from", "to", "from", "to"],
        n_targets: next,
        occs,
        n_src: n,
        journal,
    }
}

/// Shuffled world: in each projection, with its own seed, the second-port
/// targets of relation 0 are permuted among its occurrences (for the
/// lattice: of each relation). Families: the sex relation is untouched.
fn shuffle_world(w: &mut World, seed: u64, all_relations: bool) {
    for s in 0..w.n_src {
        let mut rng = Rng::new(seed, 500 + s as u64);
        let rels: Vec<usize> = if all_relations {
            (0..w.rel_names.len()).collect()
        } else {
            vec![0]
        };
        for rel in rels {
            let idx: Vec<usize> = (0..w.occs.len())
                .filter(|&i| w.occs[i].src == s && w.occs[i].rel == rel)
                .collect();
            let mut t: Vec<usize> = idx.iter().map(|&i| w.occs[i].ports[1].1).collect();
            rng.shuffle(&mut t);
            for (k, &i) in idx.iter().enumerate() {
                w.occs[i].ports[1].1 = t[k];
                w.occs[i].bad_offset = 0;
            }
        }
    }
    w.journal.push("variant shuffled".to_string());
}

/// Twin: same relations, ports and occurrence counts per projection; each
/// port target drawn uniformly from the projection's targets.
fn twin_world(w: &mut World, seed: u64) {
    for s in 0..w.n_src {
        let mut rng = Rng::new(seed, 900 + s as u64);
        let pool: Vec<usize> = w
            .occs
            .iter()
            .filter(|o| o.src == s)
            .flat_map(|o| o.ports.iter().map(|p| p.1))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        for o in w.occs.iter_mut().filter(|o| o.src == s) {
            for p in o.ports.iter_mut() {
                p.1 = pool[rng.below(pool.len() as u64) as usize];
            }
            o.bad_offset = 0;
        }
    }
    w.journal.push("variant twin".to_string());
}

fn write_world(w: &World, label_seed: u64, prefix: &str) {
    if w.occs.len() > MAX_OCCURRENCES {
        eprintln!("limit: {} occurrences", w.occs.len());
        exit(2);
    }
    let mut lab = Labels::new(label_seed);
    let rel_l: Vec<String> = w.rel_names.iter().map(|_| lab.fresh()).collect();
    let port_l: Vec<String> = w.port_names.iter().map(|_| lab.fresh()).collect();
    let src_l: Vec<String> = (0..w.n_src).map(|_| lab.fresh()).collect();
    let mut perm: Vec<usize> = (0..w.n_targets).collect();
    lab.rng.shuffle(&mut perm);
    let tgt_l: Vec<String> = (0..w.n_targets).map(|_| lab.fresh()).collect();
    let target = |t: usize| &tgt_l[perm[t]];
    let mut lines = BTreeMap::new();
    let mut journal = w.journal.clone();
    for (r, name) in w.rel_names.iter().enumerate() {
        journal.push(format!("label rel {name} {}", rel_l[r]));
    }
    for (p, name) in w.port_names.iter().enumerate() {
        journal.push(format!("label port {name} {}", port_l[p]));
    }
    for (s, l) in src_l.iter().enumerate() {
        journal.push(format!("label src {s} {l}"));
    }
    for o in &w.occs {
        let id = lab.fresh();
        if o.bad_offset != 0 {
            journal.push(format!("bad {id} offset {}", o.bad_offset));
        }
        lines.insert(
            id.clone(),
            format!(
                "occ {id} rel {} port {} -> {} port {} -> {} src {}",
                rel_l[o.rel],
                port_l[o.ports[0].0],
                target(o.ports[0].1),
                port_l[o.ports[1].0],
                target(o.ports[1].1),
                src_l[o.src]
            ),
        );
    }
    eprintln!(
        "estimate: targets {} occurrences {} projections {}",
        w.n_targets,
        w.occs.len(),
        w.n_src
    );
    let mut text = String::new();
    for l in lines.values() {
        text.push_str(l);
        text.push('\n');
    }
    fs::write(format!("{prefix}.txt"), text).unwrap();
    fs::write(format!("{prefix}.journal"), journal.join("\n") + "\n").unwrap();
}

fn permute(input: &str, seed: u64, out: &str) {
    let text = fs::read_to_string(input).unwrap();
    let mut lines: Vec<&str> = text.lines().collect();
    Rng::new(seed, 77).shuffle(&mut lines);
    fs::write(out, lines.join("\n") + "\n").unwrap();
}

/// Outside check of a mechanism report against the generator journal
/// (families world). Prints one summary line.
fn check(journal: &str, report: &str) {
    let j = fs::read_to_string(journal).unwrap();
    let r = fs::read_to_string(report).unwrap();
    let mut rel_name = BTreeMap::new();
    let mut bad: BTreeMap<String, i64> = BTreeMap::new();
    let (mut cross, mut cross_kids) = (0usize, 0usize);
    for l in j.lines() {
        let t: Vec<&str> = l.split_whitespace().collect();
        match t.as_slice() {
            ["label", "rel", name, lab] => {
                rel_name.insert(lab.to_string(), name.to_string());
            }
            ["bad", id, "offset", o] => {
                bad.insert(id.to_string(), o.parse().unwrap());
            }
            ["family", ..] => {
                for w in t.windows(2) {
                    if w[0] == "crossgen_marriages" {
                        cross += w[1].parse::<usize>().unwrap();
                    }
                    if w[0] == "crossgen_with_children" {
                        cross_kids += w[1].parse::<usize>().unwrap();
                    }
                }
            }
            _ => {}
        }
    }
    let mut fixed_shift = Vec::new();
    let (mut conds, mut refuted, mut ref_bad, mut ok_bad, mut ref_nobad, mut cancel) =
        (0, 0, 0, 0, 0, 0);
    let mut in_axis = false;
    let mut path_line = String::new();
    for l in r.lines() {
        let t: Vec<&str> = l.split_whitespace().collect();
        if t.first() == Some(&"fixed") {
            in_axis = false;
            if t.get(1) == Some(&"shift") {
                let rels: Vec<String> = t[3]
                    .split(',')
                    .map(|x| rel_name.get(x).cloned().unwrap_or("?".into()))
                    .collect();
                let status = t.last().unwrap().to_string();
                in_axis = rels == ["parent"];
                fixed_shift.push(format!("{}:{}:{}", rels.join("+"), t[5], status));
            }
        }
        if in_axis && t.first() == Some(&"cond") {
            conds += 1;
            let is_ref = t[2] == "refuted";
            let mut has_bad = false;
            let mut net = 0i64;
            for occ in &t[3..] {
                let (id, dir) = occ.split_at(occ.len() - 1);
                if let Some(o) = bad.get(id) {
                    has_bad = true;
                    net += if dir == "+" { *o } else { -*o };
                }
            }
            if is_ref {
                refuted += 1;
                if has_bad {
                    ref_bad += 1;
                } else {
                    ref_nobad += 1;
                }
            } else if has_bad {
                ok_bad += 1;
                if net == 0 {
                    cancel += 1;
                }
            }
        }
        if in_axis && t.first() == Some(&"pathcheck") {
            path_line = t[1..].join(" ");
        }
    }
    println!(
        "check fixed_shift=[{}] crossgen_marriages={cross} crossgen_with_children={cross_kids} bad_occurrences={} conds={conds} refuted={refuted} refuted_with_bad={ref_bad} refuted_without_bad={ref_nobad} ok_with_bad={ok_bad} ok_with_bad_cancelled={cancel} paths=[{path_line}]",
        fixed_shift.join(" "),
        bad.len()
    );
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let num = |i: usize| -> u64 { a[i].parse().expect("number") };
    match a.get(1).map(String::as_str) {
        Some("gen") if a.len() == 8 => {
            let (seed, n, lseed) = (num(4), num(5) as usize, num(6));
            let mut w = match a[2].as_str() {
                "families" => families(seed, n),
                "rings" => rings(seed, n),
                "lattice" => lattice(seed, n),
                _ => panic!("kind"),
            };
            match a[3].as_str() {
                "plain" => {}
                "shuffled" => shuffle_world(&mut w, seed, a[2] == "lattice"),
                "twin" => twin_world(&mut w, seed),
                _ => panic!("variant"),
            }
            write_world(&w, lseed, &a[7]);
        }
        Some("permute") if a.len() == 5 => permute(&a[2], num(3), &a[4]),
        Some("check") if a.len() == 4 => check(&a[2], &a[3]),
        _ => {
            eprintln!("usage: see module doc");
            exit(1);
        }
    }
}

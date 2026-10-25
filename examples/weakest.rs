//! H74 step 3: the weakest definitions of the small star (`docs/impl/atlas.md` §5).
//! A definition is weakest when no law in it can be swapped for one holding
//! on strictly more tables while it still singles out the same tables.

use agl::atlas::{Atlas, Set};
use std::collections::BTreeMap;

fn main() {
    let a = Atlas::build(3);
    let mut g = Set::none(a.entities.len());
    for (i, e) in a.entities.iter().enumerate() {
        if ["0", "01/10", "012/120/201"].contains(&e.to_string().as_str()) {
            g.insert(i);
        }
    }
    let content = a.content(&g);
    let mut classes: BTreeMap<Set, Vec<usize>> = BTreeMap::new();
    for &l in &content {
        classes.entry(a.holds[l].clone()).or_default().push(l);
    }
    let cls: Vec<(Set, Vec<usize>)> = classes.into_iter().collect();
    eprintln!("content {} classes {}", content.len(), cls.len());
    let all = Set::all(a.entities.len());
    let and = |x: &Set, y: &Set| x.and(y);
    let valid = |ix: &[usize]| ix.iter().fold(all.clone(), |m, &i| and(&m, &cls[i].0)) == g;
    let weaker = |i: usize, j: usize| cls[i].0.within(&cls[j].0) && cls[i].0 != cls[j].0;
    let mut defs: Vec<Vec<usize>> = Vec::new();
    let k = cls.len();
    for i in 0..k {
        for j in i + 1..k {
            if valid(&[i, j]) {
                defs.push(vec![i, j]);
            }
            for l in j + 1..k {
                let d = [i, j, l];
                if valid(&d) && !valid(&[i, j]) && !valid(&[i, l]) && !valid(&[j, l]) {
                    defs.push(d.to_vec());
                }
            }
        }
    }
    eprintln!("irredundant definitions {}", defs.len());
    let weakest: Vec<&Vec<usize>> = defs
        .iter()
        .filter(|d| {
            d.iter().enumerate().all(|(p, &c)| {
                (0..k).all(|w| {
                    if !weaker(c, w) {
                        return true;
                    }
                    let mut e = d.to_vec();
                    e[p] = w;
                    !valid(&e)
                })
            })
        })
        .collect();
    eprintln!("weakest {}", weakest.len());
    let class_of = |s: &str| {
        cls.iter()
            .position(|(_, ls)| ls.iter().any(|&l| a.laws[l].to_string() == s))
            .unwrap()
    };
    let mut t: Vec<usize> = [
        "∀x∀y∀z: x·(y·z) = (x·y)·z",
        "∀x∀y∃z: x = y·z",
        "∀x∀y∃z: x = z·y",
    ]
    .iter()
    .map(|s| class_of(s))
    .collect();
    t.sort();
    eprintln!(
        "triple classes {t:?} sizes {:?} valid {} in defs {} weakest {}",
        t.iter().map(|&c| cls[c].1.len()).collect::<Vec<_>>(),
        valid(&t),
        defs.contains(&t),
        weakest.contains(&&t)
    );
    for (p, &c) in t.iter().enumerate() {
        for w in 0..k {
            if weaker(c, w) {
                let mut e = t.clone();
                e[p] = w;
                if valid(&e) {
                    eprintln!(
                        "  {} -> {} [{} laws]",
                        a.laws[cls[c].1[0]],
                        a.laws[cls[w].1[0]],
                        cls[w].1.len()
                    );
                }
            }
        }
    }
    for &c in &t {
        for &l in &cls[c].1 {
            eprintln!("  class {c}: {}", a.laws[l]);
        }
    }
}

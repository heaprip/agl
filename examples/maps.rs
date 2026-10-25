//! H74 §6: the layer of maps of three points against the fork of the small
//! layer (`docs/impl/atlas.md` §6).

use agl::atlas::{Atlas, Law, Set, generated, models_sat};
use std::time::Instant;

fn main() {
    let t = Instant::now();
    let points: u8 = std::env::args().nth(1).map_or(3, |s| s.parse().unwrap());
    let layer = generated(points, 8);
    let sizes: Vec<u8> = layer.iter().map(|t| t.n).collect();
    eprintln!(
        "layer {} entities, sizes {sizes:?} {:?}",
        layer.len(),
        t.elapsed()
    );
    let (a, own) = Atlas::with(3, &layer);
    eprintln!("atlas {} entities {:?}", a.entities.len(), t.elapsed());
    let trunk = a.content(&own);
    eprintln!("trunk of the layer: {} laws", trunk.len());
    for &l in trunk.iter().take(12) {
        eprintln!("  {}", a.laws[l]);
    }
    let small = {
        let mut s = Set::none(a.entities.len());
        (0..a.entities.len())
            .filter(|&i| a.entities[i].n <= 3)
            .for_each(|i| s.insert(i));
        s
    };
    // The small star: the entities of size <= 3 where the shortest
    // definition of section 4 holds.
    let d0: Vec<usize> = ["∀x∀y: x·(y·x) = (x·x)·y", "∀x∀y∃z: x = y·z"]
        .iter()
        .map(|s| a.laws.iter().position(|l| l.to_string() == *s).unwrap())
        .collect();
    let g = a.extent(&d0).and(&small);
    eprintln!("small star {}", g.count());
    let defs = a.definitions(&g, &small);
    eprintln!("definitions {} {:?}", defs.len(), t.elapsed());
    let br = a.branches(&defs, &own);
    eprintln!("branches {}", br.len());
    for (s, ds) in br.iter().take(8) {
        let es: Vec<String> = (0..a.entities.len())
            .filter(|&i| s.contains(i))
            .map(|i| a.entities[i].to_string())
            .collect();
        let shortest = ds.iter().min_by_key(|d| d.len()).unwrap();
        let names: Vec<String> = shortest.iter().map(|&l| a.laws[l].to_string()).collect();
        println!(
            "{} defs, entities {:?}\n   shortest: {}",
            ds.len(),
            es,
            names.join(" & ")
        );
        let within = br.iter().all(|(o, _)| o.within(s));
        println!("   contains all others: {within}");
    }
    let (pos, ds) = &br[0];
    // Most specific: no law can be swapped for a strictly stronger one that
    // still holds on every generated entity of the branch.
    let specific: Vec<&Vec<usize>> = ds
        .iter()
        .filter(|d| {
            d.iter().all(|&l| {
                !(0..a.laws.len()).any(|m| {
                    a.holds[m].within(&a.holds[l])
                        && a.holds[m] != a.holds[l]
                        && pos.within(&a.holds[m])
                })
            })
        })
        .collect();
    println!("widest {} defs, most specific {}", ds.len(), specific.len());
    let mut tally = std::collections::BTreeMap::new();
    for d in &specific {
        let yes: Vec<&Law> = d.iter().map(|&l| &a.laws[l]).collect();
        let top: u8 = std::env::args().nth(2).map_or(6, |s| s.parse().unwrap());
        let c: Vec<usize> = (1..=top)
            .map(|n| models_sat(n, &yes, &[]).0.len())
            .collect();
        println!("{c:?} {:?}", t.elapsed());
        *tally.entry(c).or_insert(0) += 1;
    }
    println!("{tally:?} {:?}", t.elapsed());
}

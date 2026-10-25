//! H74 §8: products and factors of the entities of the S boundary
//! (`docs/impl/atlas.md` §8).

use agl::atlas::{Law, factorizations, language, models_sat, splits};

fn main() {
    let lang = language();
    let law = |s: &str| lang.iter().find(|l| l.to_string() == s).unwrap();
    // A definition of the S boundary of the widest branch (§7).
    let d: Vec<&Law> = [
        "∀x∀y∃z: x = y·z",
        "∀x∀y∃z: x = z·y",
        "∀x∀y∀z: x·(y·z) = (x·y)·z",
    ]
    .iter()
    .map(|s| law(s))
    .collect();
    let max: u8 = std::env::args().nth(1).map_or(8, |s| s.parse().unwrap());
    let ents: Vec<_> = (1..=max).flat_map(|n| models_sat(n, &d, &[]).0).collect();
    let sp = splits(&ents);
    for (i, e) in ents.iter().enumerate() {
        let f: Vec<Vec<u8>> = factorizations(&sp, i)
            .iter()
            .map(|f| f.iter().map(|&k| ents[k].n).collect())
            .collect();
        let kind = if e.n == 1 {
            "one"
        } else if sp[i].is_empty() {
            "prime"
        } else {
            "composite"
        };
        println!("#{i} n = {} {kind} {f:?}", e.n);
    }
}

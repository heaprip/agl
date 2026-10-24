//! Atom census: how much of a closure is nesting (H61 label prototype).
//!
//! Evaluates each file in the empty plane and prints, by relation, the atoms
//! held and the premises recorded for them, largest first.
//!
//!     cargo run --release --example census -- cases/kinship.agl cases/trunk/oxygen.agl

use std::collections::BTreeMap;

use agl::eval::evaluate;
use agl::model::Plane;

fn main() {
    for path in std::env::args().skip(1) {
        let prog = agl::parse_file(std::path::Path::new(&path)).expect("parse");
        let out = evaluate(&prog, &Plane::new());
        assert!(!out.truncated, "{path}: closure truncated");
        // relation -> (atoms, derivations, premises)
        let mut by: BTreeMap<&str, (usize, usize, usize)> = BTreeMap::new();
        for (atom, ders) in out.db.values() {
            let e = by.entry(atom.rel.as_str()).or_default();
            e.0 += 1;
            e.1 += ders.len();
            e.2 += ders.iter().map(|d| d.premises.len()).sum::<usize>();
        }
        let total: usize = by.values().map(|v| v.0).sum();
        let mut rows: Vec<_> = by.into_iter().collect();
        rows.sort_by(|a, b| b.1.0.cmp(&a.1.0).then(a.0.cmp(b.0)));
        println!(
            "== {path}: {total} atoms, {} facts, {} rules",
            prog.facts.len(),
            prog.rules.len()
        );
        for (rel, (n, d, p)) in rows.iter().take(8) {
            println!("  {rel:24} {n:7} atoms {d:7} derivations {p:8} premises");
        }
    }
}

//! Development from nothing into the journal (`docs/impl/atlas.md` §9).
//!
//! No input: the language of laws, every table of up to three elements and
//! the layer of maps of `points` points are made; every entity of that
//! layer gives a microtheory (the closure of its laws), and its slice of
//! small tables is a starting point, so nothing is chosen. For each start:
//! definitions within the small tables, their branches on the layer, the
//! widest, its S boundary, and a check forward by model search.  Equal model
//! counts are recorded as an observation, but do not anchor a species: equal
//! cardinalities need not name equal model classes, and all definitions were
//! checked by the same line of evidence.

use crate::atlas::{Atlas, Law, Set, Table, generated, models_upto};
use crate::journal::Journal;
use std::collections::BTreeMap;

/// Classes per size above which a check forward stops counting.
pub const LIMIT: usize = 64;

/// Entities of more elements are written as size and hash, not as tables:
/// the layer they come from makes them again.
pub const MAX_TABLE: u8 = 8;

/// Definitions per start above which the start is left unexplored.
pub const MAX_DEFS: usize = 100_000;

pub fn develop(points: u8, top: u8) -> Journal {
    let mut j = Journal::new();
    let layer = generated(points, 8);
    let (a, own) = Atlas::with(3, &layer);
    let k = a.entities.len();
    let small = {
        let mut s = Set::none(k);
        (0..k)
            .filter(|&i| a.entities[i].n <= 3)
            .for_each(|i| s.insert(i));
        s
    };
    let texts = |ix: &mut dyn Iterator<Item = usize>| -> String {
        ix.map(|i| a.entities[i].to_string())
            .collect::<Vec<_>>()
            .join(",")
    };
    let laws: Vec<String> = a.laws.iter().map(|l| l.to_string()).collect();
    let r_lang = j.add(
        "language",
        "enumerate",
        "depth<=2",
        false,
        &[],
        &format!("{} laws", laws.len()),
    );
    let r_small = j.add(
        "layer",
        "all-tables",
        "n<=3",
        false,
        &[],
        &format!("{} entities", small.count()),
    );
    let r_maps = j.add(
        "layer",
        "maps",
        &format!("points={points}"),
        false,
        &[],
        &format!("{} entities", own.count()),
    );
    let mut ent: BTreeMap<usize, u64> = BTreeMap::new();
    for i in (0..k).filter(|&i| own.contains(i)) {
        let id = j.add(
            "entity",
            "generate",
            &format!("points={points}"),
            false,
            &[r_maps],
            &shown(&a.entities[i]),
        );
        ent.insert(i, id);
    }
    let trunk: Vec<&str> = a.content(&own).iter().map(|&l| laws[l].as_str()).collect();
    j.add(
        "trunk",
        "content",
        &format!("points={points}"),
        false,
        &[r_maps, r_lang],
        &trunk.join(" ; "),
    );

    let mut starts: BTreeMap<Set, Vec<usize>> = BTreeMap::new();
    for e in (0..k).filter(|&i| own.contains(i)) {
        let mut one = Set::none(k);
        one.insert(e);
        starts
            .entry(a.extent(&a.content(&one)).and(&small).and(&own))
            .or_default()
            .push(e);
    }
    for (slice, seeds) in &starts {
        if j.full() {
            j.add(
                "stop",
                "journal-full",
                "-",
                false,
                &[],
                &format!("over {} bytes", crate::journal::MAX_BYTES),
            );
            break;
        }
        let from: Vec<u64> = seeds
            .iter()
            .map(|e| ent[e])
            .chain([r_small, r_lang])
            .collect();
        let r_mt = j.add(
            "microtheory",
            "closure",
            "n<=3",
            false,
            &from,
            &texts(&mut (0..k).filter(|&i| slice.contains(i))),
        );
        let (defs, over) = a.definitions_upto(slice, &small, MAX_DEFS);
        if over {
            let body = format!("more than {MAX_DEFS} definitions, not explored");
            j.add("definition", "too-many", "laws<=3", false, &[r_mt], &body);
            continue;
        }
        if defs.is_empty() {
            j.add(
                "definition",
                "none",
                "laws<=3",
                false,
                &[r_mt],
                "no definition of up to three laws",
            );
            continue;
        }
        let br = a.branches(&defs, &own);
        let (top_set, in_top) = &br[0];
        let nested = br.iter().all(|(s, _)| s.within(top_set));
        let r_br = j.add(
            "branch",
            "widest",
            &format!("points={points}"),
            false,
            &[r_mt, r_maps],
            &format!(
                "{} of {} definitions, {} branches, {}; holds on {}",
                in_top.len(),
                defs.len(),
                br.len(),
                if nested { "nested" } else { "not nested" },
                texts(&mut (0..k).filter(|&i| top_set.contains(i)))
            ),
        );
        let spec = a.specific(in_top, top_set);
        if spec.is_empty() {
            j.add(
                "definition",
                "s-boundary",
                &format!("points={points}"),
                false,
                &[r_br],
                "empty",
            );
            continue;
        }
        let mut counts: Vec<Vec<String>> = Vec::new();
        let mut r_defs = Vec::new();
        for d in &spec {
            let names: Vec<&str> = d.iter().map(|&l| laws[l].as_str()).collect();
            r_defs.push(j.add(
                "definition",
                "s-boundary",
                &format!("points={points}"),
                false,
                &[r_br],
                &names.join(" & "),
            ));
            let yes: Vec<&Law> = d.iter().map(|&l| &a.laws[l]).collect();
            counts.push(
                (1..=top)
                    .map(|n| {
                        let c = models_upto(n, &yes, &[], LIMIT).0.len();
                        if c > LIMIT {
                            format!("{LIMIT}+")
                        } else {
                            c.to_string()
                        }
                    })
                    .collect(),
            );
        }
        let body: Vec<String> = counts.iter().map(|c| c.join(",")).collect();
        j.add(
            "species",
            "check-forward-counts",
            &format!("n<={top}"),
            false,
            &r_defs,
            &body.join(" / "),
        );
    }
    j
}

/// A table as written in the journal.
fn shown(t: &Table) -> String {
    if t.n <= MAX_TABLE {
        return t.to_string();
    }
    let mut h: u64 = 0xcbf29ce484222325;
    for b in t.to_string().bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("n={} table#{h:016x}", t.n)
}

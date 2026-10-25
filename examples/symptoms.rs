//! Symptom table of the hidden magnitude (H73, `docs/impl/scale.md` §7), for
//! reading without the mechanics: one row per world from
//! `tools/hidden_world.py`. The hidden weights come from the comment of each
//! file, read here only.
//!
//!     cargo run --release --example symptoms -- target/scratch/hw/*.agl

use agl::bank::relations;
use agl::scale::{evidence, fechner_plates, measure, roles, steps_flat};

fn main() {
    println!(
        "world                      | against truth: order measure | plates: decided missed | flat"
    );
    for path in std::env::args().skip(1) {
        let prog = agl::parse_file(std::path::Path::new(&path)).unwrap();
        let (rels, domain, _) = relations(&prog);
        let n = domain.len();
        let src = std::fs::read_to_string(&path).unwrap();
        let mut w = vec![f64::NAN; n];
        if let Some(line) = src.lines().find(|l| l.starts_with("# hidden: ")) {
            for kv in line["# hidden: ".len()..].split_whitespace() {
                let (k, v) = kv.split_once('=').unwrap();
                if let Some(at) = domain.iter().position(|d| d.as_str() == k) {
                    w[at] = v.parse().unwrap();
                }
            }
        }
        let name = std::path::Path::new(&path)
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();
        let Some(&(pi, ii)) = roles(&rels).first() else {
            println!("{name:<26} | no roles");
            continue;
        };
        let (p, i) = (&rels[pi].1, &rels[ii].1);
        let pairs = |f: &dyn Fn(usize, usize) -> bool| {
            (0..n)
                .flat_map(|x| (0..n).map(move |y| (x, y)))
                .filter(|&(x, y)| f(x, y))
                .count()
        };
        let truth = !w[0].is_nan();
        let t = evidence(p, i);
        let order = if truth {
            pairs(&|x, y| t.get(x, y) && w[x] < w[y]).to_string()
        } else {
            "-".into()
        };
        let meas = match (measure(p, i), truth) {
            (Some(h), true) => pairs(&|x, y| h[x] >= h[y] + 2 && w[x] < w[y]).to_string(),
            (Some(_), false) => "found".into(),
            (None, _) => "none".into(),
        };
        let pl = fechner_plates(p, i);
        let (d, m, c) = pl.iter().fold((0, 0, 0), |(d, m, c), x| {
            (d + x.decided, m + x.missed, c + x.checked)
        });
        let ma: usize = pl.iter().map(|x| x.missed_alike).sum();
        println!(
            "{name:<26} | {order:>13} {meas:>7} | {d:>3}/{c:<3} decided, {m:>2} missed ({:>2}%), {ma:>2} as alike | {}",
            (100 * m).checked_div(d).unwrap_or(0),
            steps_flat(&pl, n)
        );
    }
}

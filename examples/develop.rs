//! Development from nothing into the journal: `develop POINTS TOP FILE`.

use agl::develop::develop;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let points: u8 = args.get(1).map_or(3, |s| s.parse().unwrap());
    let top: u8 = args.get(2).map_or(6, |s| s.parse().unwrap());
    let t = Instant::now();
    let j = develop(points, top);
    let text = j.text();
    match args.get(3) {
        Some(path) => std::fs::write(path, &text).unwrap(),
        None => print!("{text}"),
    }
    let anchored = j.records.iter().filter(|r| r.anchored).count();
    eprintln!(
        "{} records, {anchored} anchored, {:?}",
        j.records.len(),
        t.elapsed()
    );
}

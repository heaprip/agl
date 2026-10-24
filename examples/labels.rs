//! Nesting labels on whole ontologies (H61, step 1).
//!
//!     python3 tools/onto_stats.py edges chebi 255 > target/scratch/chebi255.tsv
//!     cargo run --release --example labels -- target/scratch/chebi255.tsv
//!     cargo run --release --example labels -- OLD.tsv NEW.tsv    # relabelling between releases
//!
//! One file: nodes, edges, intervals, and the closure size read from the
//! labels (sum of ancestors, self excluded). Two files: for nodes in both,
//! how many changed their number, their intervals, and their set of
//! descendants by name. Time and memory are measured outside (`time -l`):
//! the kernel reads no clock.

use agl::label::Labels;

fn load(path: &str) -> (usize, Labels) {
    let text = std::fs::read_to_string(path).expect("read edges");
    let edges: Vec<(&str, &str)> = text
        .lines()
        .map(|l| l.split_once('\t').expect("species<TAB>genus"))
        .collect();
    let n = edges.len();
    (n, Labels::build(edges))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (n_edges, a) = load(&args[0]);
    let closure: usize = a.names().map(|b| a.descendant_count(b) - 1).sum();
    let max_iv = a
        .names()
        .map(|b| a.intervals(b).unwrap().len())
        .max()
        .unwrap_or(0);
    println!(
        "{}: {} nodes, {n_edges} edges, {} intervals (max {max_iv} on one node), closure {closure}",
        args[0],
        a.len(),
        a.interval_count()
    );
    if let Some(path) = args.get(1) {
        let (n_edges, b) = load(path);
        println!(
            "{path}: {} nodes, {n_edges} edges, {} intervals",
            b.len(),
            b.interval_count()
        );
        let common: Vec<&str> = a.names().filter(|x| b.number(x).is_some()).collect();
        let (mut num, mut iv, mut desc) = (0, 0, 0);
        for &x in &common {
            num += usize::from(a.number(x) != b.number(x));
            iv += usize::from(a.intervals(x) != b.intervals(x));
            let mut da = a.descendants(x);
            let mut db = b.descendants(x);
            da.sort_unstable();
            db.sort_unstable();
            desc += usize::from(da != db);
        }
        let pct = |k: usize| 100.0 * k as f64 / common.len() as f64;
        println!(
            "common {}: number changed {num} ({:.1} %), intervals changed {iv} ({:.1} %), descendants changed {desc} ({:.1} %)",
            common.len(),
            pct(num),
            pct(iv),
            pct(desc)
        );
    }
}

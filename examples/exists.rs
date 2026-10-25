use agl::atlas::{Law, language};
use agl::exists::{prove, skolemize};
use agl::journal::Journal;
use agl::rewrite::Theory;
use std::time::Instant;
fn main() {
    let path = std::env::args().nth(1).unwrap();
    let j = Journal::parse(&std::fs::read_to_string(path).unwrap()).unwrap();
    let lang = language();
    let law = |s: &str| {
        lang.iter()
            .find(|l| l.to_string() == s)
            .unwrap_or_else(|| panic!("{s}"))
            .clone()
    };
    for sp in j
        .records
        .iter()
        .filter(|r| r.kind == "species" && r.anchored)
    {
        println!("species anchored={} {}", sp.anchored, sp.body);
        let defs: Vec<Vec<Law>> = sp
            .from
            .iter()
            .map(|id| j.get(*id).unwrap().body.split(" & ").map(law).collect())
            .collect();
        for (i, a) in defs.iter().enumerate() {
            let t = Instant::now();
            let sk = skolemize(&a.iter().collect::<Vec<_>>());
            let mut th = Theory::complete_exprs(&sk.axioms);
            print!(
                "D{i}: finished {} laws {} ({:?}) |",
                th.finished,
                th.laws.len(),
                t.elapsed()
            );
            for (k, b) in defs.iter().enumerate() {
                let ok = b.iter().all(|l| prove(&mut th, &sk, l).is_some());
                print!(" {}", if ok { k.to_string() } else { "-".into() });
            }
            println!(" ({:?})", t.elapsed());
            if std::env::var("SHOW").is_ok() {
                for l in th.show() {
                    println!("    {l}");
                }
            }
        }
    }
}

//! H75 stage A2: β-reduction in one universe of finite relations. For each
//! redex (λx.M)N of closed terms up to a size, and its contractum M[N/x]:
//! the least limit N from which both sides agree on tokens of size ≤ m at
//! every larger limit up to the top. Usage: universe m top size.
use agl::universe::{Ask, L, Universe};
use std::time::Instant;
fn main() {
    let arg = |i: usize, d: usize| std::env::args().nth(i).map_or(d, |s| s.parse().unwrap());
    let (m, top, size) = (arg(1, 3) as u32, arg(2, 11) as u32, arg(3, 7));
    let us: Vec<Universe> = (m..=top).map(Universe::new).collect();
    let mut redexes = Vec::new();
    for s in 1..=size {
        for t in L::all(s, 0) {
            if let L::App(f, a) = &t
                && let L::Lam(body) = &**f
            {
                redexes.push((t.clone(), body.put(0, a)));
            }
        }
    }
    let t0 = Instant::now();
    // Redexes go round the cores; each core keeps one asker per limit, so
    // what one redex learned serves the next. Results come back in order.
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let askers = cores * us.len();
    let keys: Vec<(String, String)> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..cores)
            .map(|c| {
                let (us, redexes) = (&us, &redexes);
                sc.spawn(move || {
                    let mut asks: Vec<Ask> = us.iter().map(|u| Ask::sharing(u, askers)).collect();
                    let mut out = Vec::new();
                    for (i, (lhs, rhs)) in redexes.iter().enumerate().skip(c).step_by(cores) {
                        let mut agree = Vec::new();
                        for a in asks.iter_mut() {
                            match (a.element(lhs, m), a.element(rhs, m)) {
                                (Some(l), Some(r)) => agree.push(l == r),
                                _ => break,
                            }
                        }
                        let key = if agree.len() < us.len() {
                            "undecided".to_string()
                        } else if !agree[agree.len() - 1] {
                            "not yet".to_string()
                        } else {
                            let from = agree.iter().rposition(|&x| !x).map_or(0, |i| i + 1);
                            format!("N={}", m as usize + from)
                        };
                        out.push((i, (key, format!("{lhs} -> {rhs}"))));
                    }
                    out
                })
            })
            .collect();
        let mut all: Vec<_> = hs.into_iter().flat_map(|h| h.join().unwrap()).collect();
        all.sort_by_key(|(i, _)| *i);
        all.into_iter().map(|(_, k)| k).collect()
    });
    let mut hist = std::collections::BTreeMap::new();
    for (key, what) in &keys {
        if key == "not yet" || key == "undecided" {
            println!("{key} at N={top}: {what}");
        }
        *hist.entry(key.clone()).or_insert(0) += 1;
    }
    println!(
        "m={m}, N up to {top}, {} redexes of size <= {size}: {hist:?} in {:?}",
        redexes.len(),
        t0.elapsed()
    );
}

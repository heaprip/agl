//! H75 stage A2: β-reduction in one universe of finite relations. For each
//! redex (λx.M)N of closed terms up to a size, and its contractum M[N/x]:
//! the least limit N from which both sides agree on tokens of size ≤ m at
//! every larger limit up to the top. Usage: universe m top size.
#[path = "../tests/star/mod.rs"]
mod star;
use agl::universe::{Find, Universe};
use star::{L, of};
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
    // One limit at a time, one finder for all redexes: what one learned
    // serves the next, and the memory bound is the finder's alone.
    let mut agree: Vec<Vec<Option<bool>>> = vec![Vec::new(); redexes.len()];
    let formulas: Vec<_> = redexes.iter().map(|(l, r)| (of(l), of(r))).collect();
    for u in &us {
        let mut f = Find::new(u);
        for (i, (fl, fr)) in formulas.iter().enumerate() {
            let a = match (f.element(fl, m), f.element(fr, m)) {
                (Some(l), Some(r)) => Some(l == r),
                _ => None,
            };
            agree[i].push(a);
        }
    }
    let mut hist = std::collections::BTreeMap::new();
    for ((lhs, rhs), a) in redexes.iter().zip(&agree) {
        let key = if let Some(p) = a.iter().position(|x| x.is_none()) {
            println!("undecided at N={}: {lhs} -> {rhs}", m as usize + p);
            "undecided".to_string()
        } else if a[a.len() - 1] == Some(false) {
            println!("not yet at N={top}: {lhs} -> {rhs}");
            "not yet".to_string()
        } else {
            let from = a
                .iter()
                .rposition(|&x| x == Some(false))
                .map_or(0, |i| i + 1);
            format!("N={}", m as usize + from)
        };
        *hist.entry(key).or_insert(0) += 1;
    }
    println!(
        "m={m}, N up to {top}, {} redexes of size <= {size}: {hist:?} in {:?}",
        redexes.len(),
        t0.elapsed()
    );
}

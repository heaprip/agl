//! Nesting labels against the closure by traversal (H61).
//! `AGL_SIM_SEEDS=<n>` widens the sweep, `AGL_SEED=<n>` replays one seed.

use agl::label::Labels;
use agl::sim::Rng;

fn seeds() -> Vec<u64> {
    if let Ok(s) = std::env::var("AGL_SEED") {
        return vec![s.parse().expect("AGL_SEED must be a number")];
    }
    let n: u64 = std::env::var("AGL_SIM_SEEDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(2000);
    (0..n).collect()
}

/// A random graph: edges mostly go from a later node to an earlier one; on
/// odd seeds a few go back, making cycles (self-loops included). Names are
/// shuffled so that name order is not the build order.
fn graph(seed: u64) -> (Vec<String>, Vec<(usize, usize)>) {
    let mut rng = Rng::new(seed);
    let n = 1 + rng.below(30);
    let mut names: Vec<String> = (0..n).map(|i| format!("c{i:02}")).collect();
    rng.shuffle(&mut names);
    let mut edges = Vec::new();
    for a in 1..n {
        let k = rng.below(4);
        for _ in 0..k {
            edges.push((a, rng.below(a)));
        }
    }
    if seed % 2 == 1 {
        for _ in 0..rng.below(4) {
            let a = rng.below(n);
            edges.push((a, a + rng.below(n - a)));
        }
    }
    (names, edges)
}

fn closure(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<bool>> {
    let mut up = vec![vec![false; n]; n];
    for (a, row) in up.iter_mut().enumerate() {
        let mut stack = vec![a];
        while let Some(x) = stack.pop() {
            if row[x] {
                continue;
            }
            row[x] = true;
            stack.extend(edges.iter().filter(|e| e.0 == x).map(|e| e.1));
        }
    }
    up
}

#[test]
fn labels_match_closure() {
    for seed in seeds() {
        let (names, edges) = graph(seed);
        let named: Vec<(&str, &str)> = edges
            .iter()
            .map(|&(a, b)| (names[a].as_str(), names[b].as_str()))
            .collect();
        let labels = Labels::build(named.iter().copied());
        let up = closure(names.len(), &edges);
        for a in 0..names.len() {
            for b in 0..names.len() {
                // Isolated nodes are not in any edge; they are within themselves only.
                assert_eq!(
                    labels.within(&names[a], &names[b]),
                    up[a][b],
                    "seed {seed}: {} within {}",
                    names[a],
                    names[b]
                );
                // One edge or more: a node reaches itself only on a cycle.
                let step = edges.iter().any(|&(x, y)| x == a && up[y][b]);
                assert_eq!(
                    labels.reaches(&names[a], &names[b]),
                    step,
                    "seed {seed}: {} reaches {}",
                    names[a],
                    names[b]
                );
            }
            if labels.number(&names[a]).is_some() {
                let mut anc = labels.ancestors(&names[a]);
                anc.sort_unstable();
                let mut want: Vec<&str> = (0..names.len())
                    .filter(|&b| up[a][b])
                    .map(|b| names[b].as_str())
                    .collect();
                want.sort_unstable();
                assert_eq!(anc, want, "seed {seed}: ancestors of {}", names[a]);
                let n_desc = (0..names.len()).filter(|&d| up[d][a]).count();
                assert_eq!(labels.descendant_count(&names[a]), n_desc, "seed {seed}");
                assert_eq!(labels.descendants(&names[a]).len(), n_desc, "seed {seed}");
            }
        }
    }
}

#[test]
fn edge_order_does_not_matter() {
    for seed in seeds() {
        let (names, edges) = graph(seed);
        let mut named: Vec<(&str, &str)> = edges
            .iter()
            .map(|&(a, b)| (names[a].as_str(), names[b].as_str()))
            .collect();
        let first = Labels::build(named.iter().copied());
        let mut rng = Rng::new(seed ^ 0x5eed);
        if !named.is_empty() {
            let dup = *rng.pick(&named);
            named.push(dup);
        }
        rng.shuffle(&mut named);
        assert_eq!(first, Labels::build(named), "seed {seed}");
    }
}

#[test]
fn self_loop_is_a_cycle() {
    let l = Labels::build([("a", "a"), ("b", "a")]);
    assert!(l.reaches("a", "a") && !l.reaches("b", "b") && l.reaches("b", "a"));
}

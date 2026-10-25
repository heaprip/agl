//! A hidden magnitude from "clearly more" (H73, step 2b, `docs/impl/scale.md`).
//!
//! The world shows only which of two things is clearly more and which two
//! cannot be told apart. Third things separate what cannot be told apart
//! (Poincaré's microscope): x is above y if x is clearly more than y, or
//! clearly more than something y cannot be told from, or cannot be told
//! from something clearly more than y. If that evidence agrees with itself,
//! its closure ranks things in a chain of classes; the place of a class is
//! the length of the chain under it, and the threshold of "clearly more" is
//! a number of steps. Which relation plays which part is read off the laws:
//! the comparison is asymmetric, the likeness symmetric.

use crate::bank::Ext;
use crate::model::Name;

fn conv(a: &Ext) -> Ext {
    let n = a.n();
    let mut out = Ext::empty(n);
    for i in 0..n {
        for j in 0..n {
            if a.get(i, j) {
                out.set(j, i);
            }
        }
    }
    out
}

fn compose(a: &Ext, b: &Ext) -> Ext {
    let n = a.n();
    let mut out = Ext::empty(n);
    for i in 0..n {
        for k in 0..n {
            if a.get(i, k) {
                for j in 0..n {
                    if b.get(k, j) {
                        out.set(i, j);
                    }
                }
            }
        }
    }
    out
}

fn union(a: &Ext, b: &Ext) -> Ext {
    let n = a.n();
    let mut out = a.clone();
    for i in 0..n {
        for j in 0..n {
            if b.get(i, j) {
                out.set(i, j);
            }
        }
    }
    out
}

fn disjoint(a: &Ext, b: &Ext) -> bool {
    let n = a.n();
    (0..n).all(|i| (0..n).all(|j| !(a.get(i, j) && b.get(i, j))))
}

/// Transitive closure: chains of any length, by induction on the length.
fn closure(a: &Ext) -> Ext {
    let n = a.n();
    let mut c = a.clone();
    for k in 0..n {
        for i in 0..n {
            if c.get(i, k) {
                for j in 0..n {
                    if c.get(k, j) {
                        c.set(i, j);
                    }
                }
            }
        }
    }
    c
}

/// Pairs (comparison, likeness) by their laws: a comparison is non-empty
/// and asymmetric (P ∩ P˘ = ∅), a likeness non-empty and symmetric (I = I˘).
pub fn roles(rels: &[(Name, Ext)]) -> Vec<(usize, usize)> {
    let asym = |a: &Ext| a.count() > 0 && disjoint(a, &conv(a));
    let sym = |a: &Ext| a.count() > 0 && *a == conv(a);
    let mut out = Vec::new();
    for (p, (_, pe)) in rels.iter().enumerate() {
        for (i, (_, ie)) in rels.iter().enumerate() {
            if p != i && asym(pe) && sym(ie) {
                out.push((p, i));
            }
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq)]
pub struct Scale {
    /// The evidence agrees with itself: T ∩ T˘ = ∅ and its closure has no
    /// cycle.
    pub consistent: bool,
    /// Classes from the bottom, when the closure ranks them in a chain.
    pub classes: Option<Vec<Vec<usize>>>,
    /// Steps of "clearly more": every k in [lo, hi]; `None` when the
    /// observations admit no single k.
    pub threshold: Option<(usize, usize)>,
}

impl Scale {
    /// Place of every thing: the class it is in, from the bottom.
    pub fn places(&self, n: usize) -> Option<Vec<usize>> {
        let classes = self.classes.as_ref()?;
        let mut at = vec![usize::MAX; n];
        for (c, members) in classes.iter().enumerate() {
            members.iter().for_each(|&x| at[x] = c);
        }
        Some(at)
    }

    /// "more" (1), "less" (-1) or "alike" (0) for x against y, by the
    /// smallest threshold.
    pub fn predict(&self, at: &[usize], x: usize, y: usize) -> Option<i8> {
        let (k, _) = self.threshold?;
        let d = at[x] as isize - at[y] as isize;
        Some(if d >= k as isize {
            1
        } else if -d >= k as isize {
            -1
        } else {
            0
        })
    }
}

/// The evidence through third things, T = P ∪ P;I ∪ I;P, closed under
/// chains.
pub fn evidence(p: &Ext, i: &Ext) -> Ext {
    closure(&union(&union(p, &compose(p, i)), &compose(i, p)))
}

/// The hidden magnitude of comparison `p` with likeness `i`.
pub fn scale(p: &Ext, i: &Ext) -> Scale {
    let n = p.n();
    let t = union(&union(p, &compose(p, i)), &compose(i, p));
    let tc = closure(&t);
    let acyclic = (0..n).all(|x| !tc.get(x, x));
    let consistent = disjoint(&t, &conv(&t)) && acyclic;
    if !consistent {
        return Scale {
            consistent,
            classes: None,
            threshold: None,
        };
    }
    // Things the closure does not separate either way share a class; the
    // classes form a chain when that is an equivalence.
    let apart = |x: usize, y: usize| tc.get(x, y) || tc.get(y, x);
    let mut classes: Vec<Vec<usize>> = Vec::new();
    for x in 0..n {
        match classes.iter_mut().find(|c| !apart(c[0], x)) {
            Some(c) => c.push(x),
            None => classes.push(vec![x]),
        }
    }
    let chain = classes.iter().all(|c| {
        c.iter().all(|&x| c.iter().all(|&y| !apart(x, y)))
            && (0..n).all(|z| c.contains(&z) || c.iter().all(|&x| apart(x, z)))
    }) && classes.iter().all(|c| {
        classes.iter().all(|d| {
            c == d || {
                let up = tc.get(d[0], c[0]);
                c.iter().all(|&x| d.iter().all(|&y| tc.get(y, x) == up))
            }
        })
    });
    if !chain {
        return Scale {
            consistent,
            classes: None,
            threshold: None,
        };
    }
    // A class is above as many classes as it is above things' classes.
    let firsts: Vec<usize> = classes.iter().map(|c| c[0]).collect();
    classes.sort_by_key(|c| firsts.iter().filter(|&&d| tc.get(c[0], d)).count());
    let mut s = Scale {
        consistent,
        classes: Some(classes),
        threshold: None,
    };
    let at = s.places(n).unwrap();
    let (mut lo, mut hi) = (1usize, usize::MAX);
    for x in 0..n {
        for y in 0..n {
            if i.get(x, y) && x != y {
                lo = lo.max(at[x].abs_diff(at[y]) + 1);
            }
            if p.get(x, y) {
                hi = hi.min(at[x].saturating_sub(at[y]));
            }
        }
    }
    if lo <= hi {
        s.threshold = Some((lo, hi.min(n)));
    }
    s
}

/// Observed pairs, unordered, in the order of the domain: (x, y, verdict
/// of x against y).
pub fn observed(p: &Ext, i: &Ext) -> Vec<(usize, usize, i8)> {
    let n = p.n();
    let mut out = Vec::new();
    for x in 0..n {
        for y in x + 1..n {
            if p.get(x, y) {
                out.push((x, y, 1));
            } else if p.get(y, x) {
                out.push((x, y, -1));
            } else if i.get(x, y) {
                out.push((x, y, 0));
            }
        }
    }
    out
}

/// One plate: the scale fitted without part `f`, and its misses on part `f`.
#[derive(Clone, Debug)]
pub struct Plate {
    pub scale: Scale,
    pub missed: usize,
    pub checked: usize,
}

/// Three plates: observed pairs split in three by their number in domain
/// order; each fit on two parts is checked on the third.
pub fn plates(p: &Ext, i: &Ext) -> [Plate; 3] {
    let n = p.n();
    let obs = observed(p, i);
    std::array::from_fn(|f| {
        let (mut pf, mut if_) = (Ext::empty(n), Ext::empty(n));
        for (k, &(x, y, v)) in obs.iter().enumerate() {
            if k % 3 == f {
                continue;
            }
            match v {
                1 => pf.set(x, y),
                -1 => pf.set(y, x),
                _ => {
                    if_.set(x, y);
                    if_.set(y, x);
                }
            }
        }
        let scale = scale(&pf, &if_);
        let at = scale.places(n);
        let (mut missed, mut checked) = (0, 0);
        for (k, &(x, y, v)) in obs.iter().enumerate() {
            if k % 3 == f {
                checked += 1;
                let guess = at.as_ref().and_then(|at| scale.predict(at, x, y));
                if guess != Some(v) {
                    missed += 1;
                }
            }
        }
        Plate {
            scale,
            missed,
            checked,
        }
    })
}

/// The plates are flat: each fit is a chain with a threshold, no two put a
/// pair in opposite order, and their thresholds share a value.
pub fn flat(plates: &[Plate; 3], n: usize) -> bool {
    let ats: Vec<Vec<usize>> = match plates
        .iter()
        .map(|pl| pl.scale.threshold.and(pl.scale.places(n)))
        .collect()
    {
        Some(v) => v,
        None => return false,
    };
    let opposite =
        |a: &[usize], b: &[usize]| (0..n).any(|x| (0..n).any(|y| a[x] > a[y] && b[x] < b[y]));
    let crossed = (0..3).any(|u| (0..3).any(|v| u != v && opposite(&ats[u], &ats[v])));
    let lo = plates
        .iter()
        .filter_map(|pl| pl.scale.threshold)
        .map(|t| t.0)
        .max();
    let hi = plates
        .iter()
        .filter_map(|pl| pl.scale.threshold)
        .map(|t| t.1)
        .min();
    !crossed && lo <= hi
}

/// Classes of the likeness closed under chains (the coarsening), and pairs
/// of the comparison that fall inside one class (the sorites).
pub fn coarsen(p: &Ext, i: &Ext) -> (Vec<Vec<usize>>, Vec<(usize, usize)>) {
    let n = p.n();
    let c = closure(&union(i, &conv(i)));
    let mut classes: Vec<Vec<usize>> = Vec::new();
    for x in 0..n {
        match classes.iter_mut().find(|k| k[0] == x || c.get(k[0], x)) {
            Some(k) => k.push(x),
            None => classes.push(vec![x]),
        }
    }
    let class_of = |x: usize| classes.iter().position(|k| k.contains(&x)).unwrap();
    let mut inside = Vec::new();
    for x in 0..n {
        for y in 0..n {
            if p.get(x, y) && class_of(x) == class_of(y) {
                inside.push((x, y));
            }
        }
    }
    (classes, inside)
}

/// Every reading of the world: roles, scale, coarsening, three plates.
pub fn render(rels: &[(Name, Ext)], domain: &[Name]) -> String {
    let n = domain.len();
    let names = |xs: &[usize]| -> String {
        xs.iter()
            .map(|&x| domain[x].to_string())
            .collect::<Vec<_>>()
            .join(" ")
    };
    let mut s = String::new();
    let roles = roles(rels);
    if roles.is_empty() {
        s += "scale: no asymmetric relation with a symmetric one\n";
    }
    for (pi, ii) in roles {
        let (p, i) = (&rels[pi].1, &rels[ii].1);
        s += &format!("scale: more = {}, alike = {}\n", rels[pi].0, rels[ii].0);
        let sc = scale(p, i);
        s += &format!("  evidence agrees: {}\n", sc.consistent);
        match &sc.classes {
            Some(cs) => {
                let chain: Vec<String> = cs.iter().map(|c| format!("[{}]", names(c))).collect();
                s += &format!("  chain of {} classes: {}\n", cs.len(), chain.join(" < "));
            }
            None => s += "  no chain\n",
        }
        match sc.threshold {
            Some((lo, hi)) => s += &format!("  threshold: k in [{lo}, {hi}] steps\n"),
            None => s += "  threshold: none\n",
        }
        let (classes, inside) = coarsen(p, i);
        s += &format!(
            "  coarsening: {} classes of `{}` by chains; `{}` inside a class: {}\n",
            classes.len(),
            rels[ii].0,
            rels[pi].0,
            inside.len()
        );
        let pl = plates(p, i);
        for (f, plate) in pl.iter().enumerate() {
            let k = plate
                .scale
                .threshold
                .map_or("none".to_string(), |(lo, hi)| format!("[{lo}, {hi}]"));
            let classes = plate.scale.classes.as_ref().map_or(0, Vec::len);
            s += &format!(
                "  plate {f}: {classes} classes, k {k}, missed {} of {}\n",
                plate.missed, plate.checked
            );
        }
        s += &format!("  plates flat: {}\n", flat(&pl, n));
        s += &render_steps(p, i, domain);
    }
    s
}

/// Fechner's measure: the length of the longest chain of the comparison
/// under each thing, its unit one noticeable step. `None` when the
/// comparison has a cycle.
pub fn fechner(p: &Ext) -> Option<Vec<usize>> {
    let n = p.n();
    let mut h = vec![0usize; n];
    // A chain has at most n − 1 steps: relax n times, then one more round
    // that still changes something means a cycle.
    for round in 0..=n {
        let mut changed = false;
        for x in 0..n {
            for y in 0..n {
                if p.get(x, y) && h[x] < h[y] + 1 {
                    h[x] = h[y] + 1;
                    changed = true;
                }
            }
        }
        if !changed {
            return Some(h);
        }
        if round == n {
            break;
        }
    }
    None
}

/// Verdict of x against y by the measure: a difference of two steps or more
/// is "more" (1) or "less" (−1), none is "alike" (0), one step is not
/// decided — the width of the unit.
pub fn by_steps(h: &[usize], x: usize, y: usize) -> Option<i8> {
    match h[x] as isize - h[y] as isize {
        d if d >= 2 => Some(1),
        d if d <= -2 => Some(-1),
        0 => Some(0),
        _ => None,
    }
}

/// One plate of the measure: fitted without part `f`, checked on it.
#[derive(Clone, Debug)]
pub struct Steps {
    pub h: Option<Vec<usize>>,
    pub decided: usize,
    pub missed: usize,
    pub checked: usize,
}

/// Three plates of Fechner's measure, split as in `plates`.
pub fn fechner_plates(p: &Ext, i: &Ext) -> [Steps; 3] {
    let n = p.n();
    let obs = observed(p, i);
    std::array::from_fn(|f| {
        let mut pf = Ext::empty(n);
        for (k, &(x, y, v)) in obs.iter().enumerate() {
            match v {
                1 if k % 3 != f => pf.set(x, y),
                -1 if k % 3 != f => pf.set(y, x),
                _ => {}
            }
        }
        let h = fechner(&pf);
        let (mut decided, mut missed, mut checked) = (0, 0, 0);
        for (k, &(x, y, v)) in obs.iter().enumerate() {
            if k % 3 == f {
                checked += 1;
                if let Some(g) = h.as_ref().and_then(|h| by_steps(h, x, y)) {
                    decided += 1;
                    if g != v {
                        missed += 1;
                    }
                }
            }
        }
        Steps {
            h,
            decided,
            missed,
            checked,
        }
    })
}

/// No pair is decided differently by two plates.
pub fn steps_flat(plates: &[Steps; 3], n: usize) -> bool {
    let hs: Option<Vec<&Vec<usize>>> = plates.iter().map(|p| p.h.as_ref()).collect();
    let Some(hs) = hs else {
        return false;
    };
    (0..n).all(|x| {
        (0..n).all(|y| {
            let mut seen: Vec<i8> = hs.iter().filter_map(|h| by_steps(h, x, y)).collect();
            seen.dedup();
            seen.windows(2).all(|w| w[0] == w[1])
        })
    })
}

/// Fechner's measure of the world, printed.
pub fn render_steps(p: &Ext, i: &Ext, domain: &[Name]) -> String {
    let n = domain.len();
    let mut s = String::new();
    let Some(h) = fechner(p) else {
        return "  measure: the comparison has a cycle, none\n".to_string();
    };
    let top = h.iter().copied().max().unwrap_or(0);
    let levels: Vec<String> = (0..=top)
        .map(|l| {
            let at: Vec<&str> = (0..n)
                .filter(|&x| h[x] == l)
                .map(|x| domain[x].as_str())
                .collect();
            format!("{l}: {}", at.join(" "))
        })
        .collect();
    s += &format!("  measure in steps: {}\n", levels.join(" | "));
    let obs = observed(p, i);
    let decided: Vec<bool> = obs
        .iter()
        .map(|&(x, y, v)| by_steps(&h, x, y).is_none_or(|g| g == v))
        .collect();
    let undecided = obs
        .iter()
        .filter(|&&(x, y, _)| by_steps(&h, x, y).is_none())
        .count();
    let wrong = decided.iter().filter(|&&ok| !ok).count();
    s += &format!(
        "  on what was seen: {} pairs, {undecided} not decided, {wrong} wrong\n",
        obs.len()
    );
    let pl = fechner_plates(p, i);
    for (f, plate) in pl.iter().enumerate() {
        s += &format!(
            "  plate {f}: decided {} of {}, missed {}\n",
            plate.decided, plate.checked, plate.missed
        );
    }
    s += &format!("  plates flat: {}\n", steps_flat(&pl, n));
    s
}

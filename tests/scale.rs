//! Step 2b of the clean world (H73, `docs/impl/scale.md`): a hidden magnitude
//! from "clearly more". The hidden weights sit in a comment of each world,
//! read here only, as the reference.

use agl::bank::{Ext, relations};
use agl::model::Name;
use agl::scale::{coarsen, evidence, flat, plates, roles, scale};

struct World {
    rels: Vec<(Name, Ext)>,
    domain: Vec<Name>,
    weights: Vec<f64>,
}

fn world(file: &str) -> World {
    let path = format!("cases/clean/{file}.agl");
    let prog = agl::parse_file(std::path::Path::new(&path)).unwrap();
    assert!(prog.clean.is_some());
    assert!(
        agl::lint::lint(&prog)
            .iter()
            .all(|d| d.code != "ready-made")
    );
    let (rels, domain, why) = relations(&prog);
    assert!(why.is_none());
    let src = std::fs::read_to_string(&path).unwrap();
    let mut weights = vec![f64::NAN; domain.len()];
    if let Some(line) = src.lines().find(|l| l.starts_with("# hidden: ")) {
        for kv in line["# hidden: ".len()..].split_whitespace() {
            let (k, v) = kv.split_once('=').unwrap();
            let at = domain.iter().position(|d| d.as_str() == k).unwrap();
            weights[at] = v.parse().unwrap();
        }
    }
    World {
        rels,
        domain,
        weights,
    }
}

fn parts(w: &World) -> (&Ext, &Ext) {
    let r = roles(&w.rels);
    assert_eq!(r.len(), 1, "one comparison and one likeness");
    let (p, i) = r[0];
    assert_eq!(w.rels[p].0.as_str(), "heavier");
    assert_eq!(w.rels[i].0.as_str(), "alike");
    (&w.rels[p].1, &w.rels[i].1)
}

/// Ordered pairs of the evidence, and those against the hidden weights.
fn against(w: &World, t: &Ext) -> (usize, usize) {
    let n = w.domain.len();
    let (mut all, mut wrong) = (0, 0);
    for x in 0..n {
        for y in 0..n {
            if t.get(x, y) {
                all += 1;
                if w.weights[x] < w.weights[y] {
                    wrong += 1;
                }
            }
        }
    }
    (all, wrong)
}

#[test]
fn criteria() {
    for file in ["weights", "weights_full", "shuffled"] {
        let w = world(file);
        let (p, i) = parts(&w);
        let n = w.domain.len();
        let sc = scale(p, i);
        let pl = plates(p, i);
        let (classes, inside) = coarsen(p, i);
        print!("{file}: agrees {}, ", sc.consistent);
        if file != "shuffled" {
            let t = evidence(p, i);
            let (all, wrong) = against(&w, &t);
            // Pairs seen as alike that third things put in order: A = B, B
            // = C, A < C, and the microscope of Poincaré.
            let seen_alike = (0..n)
                .flat_map(|x| (0..n).map(move |y| (x, y)))
                .filter(|&(x, y)| x != y && i.get(x, y) && t.get(x, y))
                .count();
            print!(
                "ordered {all} of {} pairs ({seen_alike} of them seen as alike), against weights {wrong}, ",
                n * (n - 1) / 2
            );
            // Criterion 2/4: nothing ordered against the hidden weights.
            assert_eq!(wrong, 0, "{file}");
            // Criterion 6: the coarsening collapses and shows the sorites.
            assert_eq!(classes.len(), 1, "{file}");
            assert!(!inside.is_empty(), "{file}");
        } else {
            // Criterion 5: no hidden magnitude in the control.
            assert!(!sc.consistent || sc.threshold.is_none() || !flat(&pl, n));
        }
        let missed: Vec<String> = pl
            .iter()
            .map(|x| format!("{}/{}", x.missed, x.checked))
            .collect();
        println!(
            "chain {:?}, threshold {:?}, plates {} flat {}",
            sc.classes.as_ref().map(Vec::len),
            sc.threshold,
            missed.join(" "),
            flat(&pl, n)
        );
    }
}

#[test]
fn does_not_depend_on_fact_order() {
    for file in ["weights", "shuffled"] {
        let path = format!("cases/clean/{file}.agl");
        let prog = agl::parse_file(std::path::Path::new(&path)).unwrap();
        let base = {
            let (rels, domain, _) = relations(&prog);
            agl::scale::render(&rels, &domain)
        };
        for seed in 1..=5 {
            let (rels, domain, _) = relations(&agl::sim::permute(&prog, seed));
            assert_eq!(
                agl::scale::render(&rels, &domain),
                base,
                "{file} seed {seed}"
            );
        }
    }
}

/// Pairs with h(x) ≥ h(y) + 2 whose hidden weights go the other way.
fn inversions(w: &World, h: &[usize]) -> usize {
    let n = w.domain.len();
    (0..n)
        .flat_map(|x| (0..n).map(move |y| (x, y)))
        .filter(|&(x, y)| h[x] >= h[y] + 2 && w.weights[x] < w.weights[y])
        .count()
}

/// Fechner's unit on the completed comparison (`docs/impl/scale.md` §5, §7):
/// criteria 1, 2 (full world) and 4 asserted; the plates of the world with
/// 2/3 seen are printed.
#[test]
fn fechner_criteria() {
    use agl::scale::{by_steps, fechner_plates, measure, observed, steps_flat};
    let full = world("weights_full");
    let (p, i) = parts(&full);
    let h = measure(p, i).unwrap();
    let obs = observed(p, i);
    let decided: Vec<bool> = obs
        .iter()
        .filter_map(|&(x, y, v)| by_steps(&h, x, y).map(|g| g == v))
        .collect();
    let wrong = decided.iter().filter(|&&ok| !ok).count();
    assert!(wrong * 20 <= decided.len(), "criterion 1: {wrong} wrong");
    assert!(decided.len() * 2 >= obs.len(), "criterion 1: half decided");
    assert_eq!(inversions(&full, &h), 0, "criterion 2, full");

    let part = world("weights");
    let (p, i) = parts(&part);
    let pl = fechner_plates(p, i);
    for (f, plate) in pl.iter().enumerate() {
        let h = plate.h.as_ref().unwrap();
        println!(
            "plate {f}: decided {} of {}, missed {}, against weights {}",
            plate.decided,
            plate.checked,
            plate.missed,
            inversions(&part, h)
        );
    }
    println!("flat {}", steps_flat(&pl, part.domain.len()));

    let control = world("shuffled");
    let (p, i) = parts(&control);
    let pl = fechner_plates(p, i);
    let bad = measure(p, i).is_none()
        || !steps_flat(&pl, control.domain.len())
        || pl.iter().any(|x| x.missed * 20 > x.decided);
    assert!(bad, "criterion 4");
}

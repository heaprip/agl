//! Laws as elements of a free entity (`docs/impl/atlas.md` §10).

use agl::atlas::{self, Atlas, Law, models_sat};
use agl::free::{Derived, Eq, Free, language};
use agl::rewrite::Theory;
use std::collections::BTreeSet;

/// A law's text in a form not depending on which renaming was kept: the
/// least text over renamings of x, y, z and the two sides.
fn key(text: &str) -> String {
    let (prefix, eq) = text.split_once(": ").unwrap();
    let (l, r) = eq.split_once(" = ").unwrap();
    let mut best: Option<String> = None;
    for p in ["xyz", "xzy", "yxz", "yzx", "zxy", "zyx"] {
        let ren = |s: &str| -> String {
            s.chars()
                .map(|c| match c {
                    'x' => p.as_bytes()[0] as char,
                    'y' => p.as_bytes()[1] as char,
                    'z' => p.as_bytes()[2] as char,
                    c => c,
                })
                .collect()
        };
        // Runs of one quantifier commute: sort the letters inside each run.
        let q: Vec<(char, char)> = {
            let cs: Vec<char> = ren(prefix).chars().collect();
            cs.chunks(2).map(|c| (c[0], c[1])).collect()
        };
        let mut runs: Vec<(char, char)> = Vec::new();
        let mut i = 0;
        while i < q.len() {
            let j = (i..q.len()).find(|&j| q[j].0 != q[i].0).unwrap_or(q.len());
            let mut run = q[i..j].to_vec();
            run.sort();
            runs.extend(run);
            i = j;
        }
        let pre: String = runs.iter().flat_map(|&(a, b)| [a, b]).collect();
        for (a, b) in [(ren(l), ren(r)), (ren(r), ren(l))] {
            let t = format!("{pre}: {a} = {b}");
            if best.as_ref().is_none_or(|x| t < *x) {
                best = Some(t);
            }
        }
    }
    best.unwrap()
}

#[test]
fn the_same_language_as_pairs_of_elements() {
    let f = Free::new(3, 2);
    assert_eq!(f.len(), 147);
    let new = language(&f);
    let old = atlas::language();
    assert_eq!(new.len(), old.len());
    let a: BTreeSet<String> = new.iter().map(|e| key(&e.show(&f))).collect();
    let b: BTreeSet<String> = old.iter().map(|l| key(&l.to_string())).collect();
    assert_eq!(a.len(), new.len());
    assert_eq!(a, b);
    // The same extents on every table of up to three elements.
    let at = Atlas::build(3);
    let by_key: std::collections::BTreeMap<String, &Law> =
        old.iter().map(|l| (key(&l.to_string()), l)).collect();
    for e in &new {
        let l = by_key[&key(&e.show(&f))];
        for t in &at.entities {
            assert_eq!(
                e.holds(&f, t),
                l.holds(t) == Some(true),
                "{} on {t}",
                e.show(&f)
            );
        }
    }
}

const ASSOC: &str = "∀x∀y∀z: x·(y·z) = (x·y)·z";
const COMM: &str = "∀x∀y: x·y = y·x";
const IDEM: &str = "∀x: x = x·x";

/// Laws "for all" of the language derived from `axioms` on F(3, depth),
/// and those holding on every model of the axioms up to `n`.
fn both(axioms: &[&str], depth: u8, n: u8) -> (BTreeSet<String>, BTreeSet<String>) {
    let (derived, semantic, _) = all(axioms, depth, n);
    (derived, semantic)
}

/// As `both`, with the number of classes of F(3, depth) after gluing.
fn all(axioms: &[&str], depth: u8, n: u8) -> (BTreeSet<String>, BTreeSet<String>, usize) {
    let small = Free::new(3, 2);
    let lang = language(&small);
    let find = |s: &str| {
        lang.iter()
            .find(|e| e.show(&small) == s)
            .unwrap_or_else(|| panic!("{s}"))
            .clone()
    };
    let ax: Vec<Eq> = axioms.iter().map(|s| find(s)).collect();
    let d = Derived::new(
        Free::new(3, depth),
        &ax.iter().map(|e| (e.left, e.right)).collect::<Vec<_>>(),
    );
    let universal: Vec<&Eq> = lang
        .iter()
        .filter(|e| e.prefix.iter().all(|&(_, a)| a))
        .collect();
    let derived: BTreeSet<String> = universal
        .iter()
        .filter(|e| d.equal(e.left, e.right))
        .map(|e| e.show(&small))
        .collect();
    let old = atlas::language();
    let laws: Vec<&Law> = axioms
        .iter()
        .map(|s| old.iter().find(|l| l.to_string() == *s).unwrap())
        .collect();
    let models: Vec<_> = (1..=n).flat_map(|k| models_sat(k, &laws, &[]).0).collect();
    let semantic: BTreeSet<String> = universal
        .iter()
        .filter(|e| models.iter().all(|t| e.holds(&small, t)))
        .map(|e| e.show(&small))
        .collect();
    let classes = (0..d.free.len() as u32).filter(|&e| d.find(e) == e).count();
    (derived, semantic, classes)
}

/// Laws "for all" of the language decided by normal forms: the rules
/// completed from `axioms`, and how many normal forms were built.
fn by_rules(axioms: &[&str]) -> (BTreeSet<String>, Theory) {
    let f = Free::new(3, 2);
    let lang = language(&f);
    let pairs: Vec<_> = axioms
        .iter()
        .map(|s| lang.iter().find(|e| e.show(&f) == *s).unwrap())
        .map(|e| (f.term(e.left), f.term(e.right)))
        .collect();
    let mut th = Theory::complete(&pairs);
    let derived = lang
        .iter()
        .filter(|e| e.prefix.iter().all(|&(_, a)| a))
        .filter(|e| th.ground(&f.term(e.left)) == th.ground(&f.term(e.right)))
        .map(|e| e.show(&f))
        .collect();
    (derived, th)
}

#[test]
fn derivation_is_sound_on_small_tables() {
    for axioms in [
        vec![ASSOC],
        vec![ASSOC, COMM],
        vec![COMM],
        vec![IDEM, ASSOC],
    ] {
        let (derived, semantic) = both(&axioms, 3, 3);
        let wrong: Vec<_> = derived.difference(&semantic).collect();
        assert!(wrong.is_empty(), "{axioms:?}: {wrong:?}");
        let (derived, _) = by_rules(&axioms);
        let wrong: Vec<_> = derived.difference(&semantic).collect();
        assert!(wrong.is_empty(), "{axioms:?} by rules: {wrong:?}");
    }
}

#[test]
fn syntax_meets_semantics() {
    // Commutative tables alone are too many past three elements.
    for (axioms, n) in [
        (vec![ASSOC], 5),
        (vec![ASSOC, COMM], 5),
        (vec![COMM], 3),
        (vec![IDEM, ASSOC], 5),
    ] {
        let (derived, semantic, classes) = all(&axioms, 3, n);
        // Normal forms decide the same, building fewer elements than
        // F(3, 3) has classes; completion ends except for x·x = x.
        let (rules, th) = by_rules(&axioms);
        assert_eq!(rules, semantic, "{axioms:?} by rules");
        assert!(
            th.built() <= classes,
            "{axioms:?}: {} > {classes}",
            th.built()
        );
        assert_eq!(th.finished, !axioms.contains(&IDEM), "{axioms:?}");
        let missing: Vec<_> = semantic.difference(&derived).take(5).collect();
        let wrong: Vec<_> = derived.difference(&semantic).take(5).collect();
        assert!(
            missing.is_empty() && wrong.is_empty(),
            "{axioms:?}: missing {missing:?}, wrong {wrong:?} ({} derived, {} semantic)",
            derived.len(),
            semantic.len()
        );
    }
}

#[test]
fn derivation_does_not_depend_on_order() {
    let (a, _) = both(&[IDEM, ASSOC], 3, 1);
    let (b, _) = both(&[ASSOC, IDEM], 3, 1);
    assert_eq!(a, b);
    for (x, y) in [
        ([IDEM, ASSOC], [ASSOC, IDEM]),
        ([ASSOC, COMM], [COMM, ASSOC]),
    ] {
        let (a, ta) = by_rules(&x);
        let (b, tb) = by_rules(&y);
        assert_eq!((a, ta.show()), (b, tb.show()));
    }
}

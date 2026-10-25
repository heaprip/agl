//! H74 acceptance (`docs/impl/atlas.md` §3). Known structures appear only
//! here, as stars to compare the atlas with; `src/atlas.rs` never names them.

use agl::atlas::{Atlas, Law, Set, Table, models};
use std::sync::OnceLock;

fn atlas() -> &'static Atlas {
    static A: OnceLock<Atlas> = OnceLock::new();
    A.get_or_init(|| Atlas::build(3))
}

fn op(t: &Table, a: u8, b: u8) -> u8 {
    t.get(a, b).unwrap()
}

/// The star: an associative table with a two-sided unit and inverses.
fn star_group(t: &Table) -> bool {
    let r = 0..t.n;
    let assoc = r.clone().all(|a| {
        r.clone().all(|b| {
            r.clone()
                .all(|c| op(t, op(t, a, b), c) == op(t, a, op(t, b, c)))
        })
    });
    let unit = r
        .clone()
        .find(|&e| r.clone().all(|x| op(t, e, x) == x && op(t, x, e) == x));
    assoc
        && unit.is_some_and(|e| {
            r.clone()
                .all(|x| r.clone().any(|y| op(t, x, y) == e && op(t, y, x) == e))
        })
}

fn star_commutative(t: &Table) -> bool {
    (0..t.n).all(|a| (0..t.n).all(|b| op(t, a, b) == op(t, b, a)))
}

fn groups() -> Set {
    let a = atlas();
    let mut s = Set::none(a.entities.len());
    for (i, t) in a.entities.iter().enumerate() {
        if star_group(t) {
            s.insert(i);
        }
    }
    s
}

#[test]
fn magmas_up_to_isomorphism() {
    let a = atlas();
    let count = |n| a.entities.iter().filter(|t| t.n == n).count();
    assert_eq!((count(1), count(2), count(3)), (1, 10, 3330));
}

fn law(s: &str) -> &'static Law {
    let a = atlas();
    a.laws
        .iter()
        .find(|l| l.to_string() == s)
        .unwrap_or_else(|| panic!("not in the language: {s}"))
}

fn counts(yes: &[&Law], no: &[&Law], max: u8) -> Vec<usize> {
    (1..=max).map(|n| models(n, yes, no).0.len()).collect()
}

const ASSOC: &str = "∀x∀y∀z: x·(y·z) = (x·y)·z";
const LEFT: &str = "∀x∀y∃z: x = y·z";
const RIGHT: &str = "∀x∀y∃z: x = z·y";
const COMM: &str = "∀x∀y: x·y = y·x";
const UNIT: &str = "∃x∀y: y = x·y";

#[test]
fn the_star_is_a_closed_microtheory_of_small_tables() {
    let a = atlas();
    let g = groups();
    assert_eq!(g.count(), 3);
    assert_eq!(a.extent(&a.content(&g)), g, "not closed");
    assert_eq!(a.content(&g).len(), 156);
}

/// Criterion 2 as written fails: the shortest definition on n <= 3 takes
/// two laws and goes the commutative way; at n = 5 it lets in a table that
/// breaks 70 laws of the content, at n = 6 it misses the non-commutative one.
#[test]
fn the_shortest_definition_forks_off() {
    let a = atlas();
    let d = a.definition(&groups());
    let d: Vec<String> = d.iter().map(|&l| a.laws[l].to_string()).collect();
    assert_eq!(d, ["∀x∀y: x·(y·x) = (x·x)·y", LEFT]);
    let yes = [law(&d[0]), law(&d[1])];
    assert_eq!(counts(&yes, &[], 5), [1, 1, 1, 2, 2]);
}

/// The branch of the star is in the language: three laws, all in the
/// content, give the star's counts up to n = 6.
#[test]
fn the_star_branch_exists() {
    let a = atlas();
    let yes = [law(ASSOC), law(LEFT), law(RIGHT)];
    let g = groups();
    for l in yes {
        let i = a.laws.iter().position(|m| m == l).unwrap();
        assert!(a.content(&g).contains(&i));
    }
    assert_eq!(
        a.extent(
            &a.laws
                .iter()
                .enumerate()
                .filter(|(_, l)| yes.contains(l))
                .map(|(i, _)| i)
                .collect::<Vec<_>>()
        ),
        g
    );
    assert_eq!(counts(&yes, &[], 6), [1, 1, 1, 2, 1, 2]);
    for n in 1..=6 {
        assert!(models(n, &yes, &[]).0.iter().all(star_group), "n = {n}");
    }
}

/// Criterion 3: commutativity is in the content but accidental: dropping it
/// finds one table, at n = 6, and none below.
#[test]
fn commutativity_is_accidental_for_small_tables() {
    let yes = [law(ASSOC), law(LEFT), law(RIGHT)];
    assert_eq!(counts(&yes, &[law(COMM)], 6), [0, 0, 0, 0, 0, 1]);
    let (m, _) = models(6, &yes, &[law(COMM)]);
    assert!(star_group(&m[0]) && !star_commutative(&m[0]));
}

/// Criterion 4: dropping associativity finds tables; dropping a unit, which
/// follows from the three, finds none.
#[test]
fn ablation_tells_a_free_law_from_a_consequence() {
    let free = counts(&[law(LEFT), law(RIGHT)], &[law(ASSOC)], 4);
    assert!(free.iter().sum::<usize>() > 0, "{free:?}");
    let yes = [law(ASSOC), law(LEFT), law(RIGHT)];
    assert_eq!(counts(&yes, &[law(UNIT)], 6), [0; 6]);
}

#[test]
fn search_does_not_depend_on_law_order() {
    let (f, b) = (
        [law(ASSOC), law(LEFT), law(RIGHT)],
        [law(RIGHT), law(LEFT), law(ASSOC)],
    );
    for n in 1..=5 {
        assert_eq!(models(n, &f, &[]), models(n, &b, &[]));
    }
}

/// Criterion 6, over every file of `src/`: no name of a known structure.
/// "group" is an ordinary word elsewhere in the kernel ("grouped by
/// plane"), so it is checked in the atlas only; "loop" is a keyword.
#[test]
fn no_stars_in_the_kernel() {
    let names = [
        "monoid",
        "semigroup",
        "quasigroup",
        "commutativ",
        "abelian",
        "associativ",
    ];
    for entry in std::fs::read_dir("src").unwrap() {
        let path = entry.unwrap().path();
        let text = std::fs::read_to_string(&path).unwrap().to_lowercase();
        let atlas = path.ends_with("atlas.rs");
        for word in names.iter().chain(if atlas { &["group"][..] } else { &[] }) {
            assert!(!text.contains(word), "{} names {word}", path.display());
        }
    }
}

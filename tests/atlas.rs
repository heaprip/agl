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

// Section 6: the layer of maps of points.

use agl::atlas::generated;

fn layer(points: u8) -> &'static (Atlas, Set) {
    static L3: OnceLock<(Atlas, Set)> = OnceLock::new();
    static L4: OnceLock<(Atlas, Set)> = OnceLock::new();
    let cell = if points == 3 { &L3 } else { &L4 };
    cell.get_or_init(|| Atlas::with(3, &generated(points, 8)))
}

fn small(a: &Atlas) -> Set {
    let mut s = Set::none(a.entities.len());
    (0..a.entities.len())
        .filter(|&i| a.entities[i].n <= 3)
        .for_each(|i| s.insert(i));
    s
}

fn star_in(a: &Atlas) -> Set {
    let mut s = Set::none(a.entities.len());
    (0..a.entities.len())
        .filter(|&i| a.entities[i].n <= 3 && star_group(&a.entities[i]))
        .for_each(|i| s.insert(i));
    s
}

#[test]
fn the_trunk_of_maps_has_associativity_not_commutativity() {
    let (a, own) = layer(3);
    assert_eq!(own.count(), 43);
    let trunk: Vec<String> = a
        .content(own)
        .iter()
        .map(|&l| a.laws[l].to_string())
        .collect();
    assert!(trunk.contains(&ASSOC.to_string()));
    assert!(!trunk.contains(&COMM.to_string()));
}

#[test]
fn the_star_comes_from_maps_of_three_points() {
    let (a, own) = layer(3);
    let sizes: Vec<u8> = (0..a.entities.len())
        .filter(|&i| own.contains(i) && star_group(&a.entities[i]))
        .map(|i| a.entities[i].n)
        .collect();
    assert_eq!(sizes, [1, 2, 3, 6]);
    let s3 = (0..a.entities.len())
        .find(|&i| own.contains(i) && a.entities[i].n == 6 && star_group(&a.entities[i]))
        .unwrap();
    assert!(!star_commutative(&a.entities[s3]));
}

/// The fork of the small layer, read on the layer of maps: one widest branch
/// containing every other, holding exactly on the star's entities of the
/// layer; the star triple in it, the shortest definition of section 4 not.
#[test]
fn the_layer_of_maps_settles_the_fork() {
    for (points, widest) in [
        (3, [1, 2, 3, 6].as_slice()),
        (4, &[1, 2, 3, 4, 4, 6, 8, 12, 24]),
    ] {
        let (a, own) = layer(points);
        let defs = a.definitions(&star_in(a), &small(a));
        let br = a.branches(&defs, own);
        let (top, in_top) = &br[0];
        assert!(br.iter().all(|(s, _)| s.within(top)), "{points} points");
        let mut sizes: Vec<u8> = (0..a.entities.len())
            .filter(|&i| top.contains(i))
            .map(|i| a.entities[i].n)
            .collect();
        sizes.sort();
        assert_eq!(sizes, widest, "{points} points");
        assert!(
            (0..a.entities.len())
                .filter(|&i| top.contains(i))
                .all(|i| star_group(&a.entities[i]))
        );
        let ix = |s: &str| a.laws.iter().position(|l| l.to_string() == s).unwrap();
        let mut triple = vec![ix(ASSOC), ix(LEFT), ix(RIGHT)];
        triple.sort();
        let d0 = {
            let mut d = vec![ix("∀x∀y: x·(y·x) = (x·x)·y"), ix(LEFT)];
            d.sort();
            d
        };
        assert!(in_top.contains(&triple), "{points} points");
        assert!(!in_top.contains(&d0), "{points} points");
    }
}

#[test]
fn generation_does_not_depend_on_order() {
    let mut l = generated(3, 8);
    l.reverse();
    let (b, own_b) = Atlas::with(3, &l);
    let (a, own_a) = layer(3);
    let names = |a: &Atlas, s: &Set| -> Vec<String> {
        let mut v: Vec<String> = (0..a.entities.len())
            .filter(|&i| s.contains(i))
            .map(|i| a.entities[i].to_string())
            .collect();
        v.sort();
        v
    };
    assert_eq!(names(a, own_a), names(&b, &own_b));
}

// Section 7: the CDCL search and the S boundary.

use agl::atlas::models_sat;

#[test]
fn sat_search_agrees_with_the_old_one() {
    let pool = [
        ASSOC,
        LEFT,
        RIGHT,
        COMM,
        UNIT,
        "∀x∀y: x·(y·x) = (x·x)·y",
        "∃x∃y∀z: x·z = z·y",
        "∀x: x = x·x",
    ];
    for (i, a) in pool.iter().enumerate() {
        for b in &pool[i..] {
            for c in pool {
                let (yes, no) = ([law(a), law(b)], [law(c)]);
                for n in 1..=3 {
                    assert_eq!(
                        models(n, &yes, &no).0,
                        models_sat(n, &yes, &no).0,
                        "{a} & {b} without {c}, n = {n}"
                    );
                }
            }
        }
    }
    let yes = [law(ASSOC), law(LEFT), law(RIGHT)];
    for n in 1..=5 {
        assert_eq!(
            models(n, &yes, &[]).0,
            models_sat(n, &yes, &[]).0,
            "n = {n}"
        );
    }
    assert_eq!(
        models_sat(6, &yes, &[law(COMM)]).0,
        models(6, &yes, &[law(COMM)]).0
    );
}

/// Criterion 4 as written fails: the widest branch's shortest definition
/// lets in tables beyond the star at n = 5, 6.
#[test]
fn the_widest_shortest_definition_overshoots() {
    let yes = [
        law("∃x∃y∀z: x·z = z·y"),
        law("∀x∀y: x·(x·y) = (x·x)·y"),
        law(RIGHT),
    ];
    let c: Vec<usize> = (1..=6).map(|n| models_sat(n, &yes, &[]).0.len()).collect();
    assert_eq!(c, [1, 1, 1, 2, 3, 10]);
}

/// The S boundary of the widest branch, found after that failure: every
/// definition in it gives the star's counts up to n = 6.
#[test]
fn the_s_boundary_of_the_widest_branch_gives_the_star() {
    let (a, own) = layer(3);
    let defs = a.definitions(&star_in(a), &small(a));
    let br = a.branches(&defs, own);
    let (top, in_top) = &br[0];
    let s = a.specific(in_top, top);
    assert_eq!((in_top.len(), s.len()), (59, 7));
    for d in s {
        let yes: Vec<&Law> = d.iter().map(|&l| &a.laws[l]).collect();
        let c: Vec<usize> = (1..=6).map(|n| models_sat(n, &yes, &[]).0.len()).collect();
        assert_eq!(c, [1, 1, 1, 2, 1, 2]);
    }
}

// Section 8: products and factors.

use agl::atlas::{factorizations, splits};

fn s_entities(max: u8) -> Vec<Table> {
    let yes = [law(LEFT), law(RIGHT), law(ASSOC)];
    (1..=max).flat_map(|n| models_sat(n, &yes, &[]).0).collect()
}

#[test]
fn a_product_keeps_exactly_the_shared_laws() {
    let a = atlas();
    let two: Vec<&Table> = a.entities.iter().filter(|t| t.n == 2).collect();
    for x in &two {
        for y in &two {
            let p = x.times(y);
            for l in &a.laws {
                let both = l.holds(x) == Some(true) && l.holds(y) == Some(true);
                assert_eq!(l.holds(&p) == Some(true), both, "{x} × {y}: {l}");
            }
        }
    }
}

#[test]
fn entities_factor_uniquely_into_primes() {
    let ents = s_entities(8);
    assert_eq!(ents.len(), 14);
    let sp = splits(&ents);
    let mut primes = Vec::new();
    let mut composite = Vec::new();
    for (i, e) in ents.iter().enumerate().skip(1) {
        let f = factorizations(&sp, i);
        assert_eq!(f.len(), 1, "#{i}");
        if sp[i].is_empty() {
            primes.push(e.n);
        } else {
            let mut sizes: Vec<u8> = f[0].iter().map(|&k| ents[k].n).collect();
            sizes.sort();
            composite.push(sizes);
        }
    }
    assert_eq!(primes, [2, 3, 4, 5, 6, 7, 8, 8, 8]);
    composite.sort();
    assert_eq!(
        composite,
        [vec![2, 2], vec![2, 2, 2], vec![2, 3], vec![2, 4]]
    );
}

/// The star Q8: a prime of order 8, not commutative, with one element other
/// than the unit equal to its own inverse; D4, the other such prime, has five.
#[test]
fn q8_is_a_prime_of_order_eight() {
    let ents = s_entities(8);
    let sp = splits(&ents);
    let mut involutions: Vec<usize> = Vec::new();
    for (i, t) in ents.iter().enumerate() {
        if t.n != 8 || !sp[i].is_empty() || star_commutative(t) {
            continue;
        }
        let e = (0..8).find(|&e| (0..8).all(|x| op(t, e, x) == x)).unwrap();
        involutions.push((0..8).filter(|&x| x != e && op(t, x, x) == e).count());
    }
    involutions.sort();
    assert_eq!(involutions, [1, 5]);
}

#[test]
fn factoring_does_not_depend_on_order() {
    let ents = s_entities(8);
    let mut rev = ents.clone();
    rev.reverse();
    let (a, b) = (splits(&ents), splits(&rev));
    let k = ents.len();
    for i in 0..k {
        let mut x: Vec<(u8, u8)> = a[i].iter().map(|&(p, q)| (ents[p].n, ents[q].n)).collect();
        let mut y: Vec<(u8, u8)> = b[k - 1 - i]
            .iter()
            .map(|&(p, q)| (rev[p].n.min(rev[q].n), rev[p].n.max(rev[q].n)))
            .collect();
        x.sort();
        y.sort();
        assert_eq!(x, y, "#{i}");
    }
}

//! H75 stages A2–A3 acceptance (`docs/impl/relations.md` §6, §8): formulas
//! over E and P in one universe; λ-terms only as a star (`star`), put into
//! formulas. Names of combinators live only here.
mod star;

use agl::universe::{Ask, F, Find, Universe};
use star::{L, of};

fn v(i: usize) -> L {
    L::Var(i)
}

fn k() -> L {
    L::lam(L::lam(v(1)))
}

fn s() -> L {
    let z = || v(0);
    L::lam(L::lam(L::lam(L::app(L::app(v(2), z()), L::app(v(1), z())))))
}

fn i() -> L {
    L::lam(v(0))
}

fn same(u: &Universe, a: &L, b: &L, m: u32) -> bool {
    let mut f = Find::new(u);
    f.element(&of(a), m).unwrap() == f.element(&of(b), m).unwrap()
}

/// The finder answers as the reference, term by term, on every closed term
/// up to size 6 and on raw formulas that are no term.
#[test]
fn finder_is_reference() {
    for n in [6u32, 8, 9] {
        let u = Universe::new(n);
        let mut ask = Ask::new(&u);
        let mut find = Find::new(&u);
        for size in 1..=6 {
            for t in L::all(size, 0) {
                let f = of(&t);
                assert_eq!(ask.element(&f, 4), find.element(&f, 4), "{t} at N={n}");
            }
        }
        // Formulas no term gives: leading to itself, holding itself, a set
        // within the set of what it leads to.
        let raw = [
            F::Exists(1, Box::new(F::And(vec![F::P(0, 1), F::E(1, 0)]))),
            F::Not(Box::new(F::Exists(1, Box::new(F::P(0, 1))))),
            F::Exists(
                1,
                Box::new(F::And(vec![
                    F::P(0, 1),
                    F::Not(Box::new(F::Exists(
                        2,
                        Box::new(F::And(vec![F::E(2, 0), F::Not(Box::new(F::E(2, 1)))])),
                    ))),
                ])),
            ),
        ];
        for f in &raw {
            assert_eq!(ask.element(f, 5), find.element(f, 5), "{f:?} at N={n}");
        }
    }
}

/// Criterion 2: K·A·B is A from N = 2m + 2 on, as predicted; S·K·K is I.
/// For m = 3 the bound is tight (for m = 4 it is not: N = 8 is enough).
#[test]
fn combinators() {
    let m = 3;
    for n in 2 * m + 2..=2 * m + 4 {
        let u = Universe::new(n);
        for (a, b) in [(i(), k()), (k(), i()), (s(), k())] {
            let kab = L::app(L::app(k(), a.clone()), b);
            assert!(same(&u, &kab, &a, m), "K A B at N={n}");
        }
    }
    let skk = L::app(L::app(s(), k()), k());
    assert!(same(&Universe::new(10), &skk, &i(), m));
    // Below the prediction the truncation shows: K I K and I differ.
    let kik = L::app(L::app(k(), i()), k());
    assert!(!same(&Universe::new(2 * m + 1), &kik, &i(), m));
}

/// Criterion 3: every redex of closed terms up to size 7 agrees with its
/// contractum on tokens ≤ 3 at N = 11 but one; (λx.x x)(λx.x) needs N = 14.
#[test]
fn beta() {
    let m = 3;
    let u = Universe::new(11);
    let mut find = Find::new(&u);
    let mut late = Vec::new();
    for size in 1..=7 {
        for t in L::all(size, 0) {
            let L::App(f, a) = &t else { continue };
            let L::Lam(body) = &**f else { continue };
            let r = body.put(0, a);
            if find.element(&of(&t), m).unwrap() != find.element(&of(&r), m).unwrap() {
                late.push(t.to_string());
            }
        }
    }
    assert_eq!(late, ["(λ(0 0) λ0)"]);
    let t = L::app(L::lam(L::app(v(0), v(0))), i());
    assert!(same(&Universe::new(14), &t, &L::app(i(), i()), m));
}

/// Criterion 4: a question past its steps is left undecided, not answered.
#[test]
fn limit() {
    let u = Universe::new(10);
    let t = of(&L::app(L::lam(L::app(v(0), v(0))), i()));
    let mut find = Find::new(&u);
    find.limit = 10;
    assert_eq!(find.element(&t, 3), None);
    find.limit = agl::universe::MAX_TOUCHED;
    assert!(find.element(&t, 3).is_some());
}

/// Criterion 5: the same answers whatever was asked before.
#[test]
fn determinism() {
    let u = Universe::new(9);
    let fs: Vec<F> = (1..=6).flat_map(|s| L::all(s, 0)).map(|t| of(&t)).collect();
    let fresh: Vec<_> = fs.iter().map(|f| Find::new(&u).element(f, 3)).collect();
    let mut find = Find::new(&u);
    let mut shared: Vec<_> = fs.iter().rev().map(|f| find.element(f, 3)).collect();
    shared.reverse();
    assert_eq!(fresh, shared);
}

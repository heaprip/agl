//! H75 stage A2 acceptance (`docs/impl/relations.md` §6): combinators and
//! β-reduction in one universe of finite relations. Names of combinators
//! live only here.
use agl::universe::{Ask, L, Universe};

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
    let mut ask = Ask::new(u);
    let (x, y) = (ask.element(a, m).unwrap(), ask.element(b, m).unwrap());
    x == y
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
/// contractum on tokens ≤ 3 from some N on; (λx.x x)(λx.x) needs N = 14.
#[test]
fn beta() {
    let m = 3;
    let us: Vec<Universe> = (m..=11).map(Universe::new).collect();
    let mut late = Vec::new();
    for size in 1..=7 {
        for t in L::all(size, 0) {
            let L::App(f, a) = &t else { continue };
            let L::Lam(body) = &**f else { continue };
            let r = body.put(0, a);
            let mut asks: Vec<Ask> = us.iter().map(Ask::new).collect();
            let last = asks.last_mut().unwrap();
            if last.element(&t, m).unwrap() != last.element(&r, m).unwrap() {
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
    let mut ask = Ask::new(&u);
    ask.limit = 1000;
    let t = L::app(L::lam(L::app(v(0), v(0))), i());
    assert_eq!(ask.element(&t, 3), None);
    ask.limit = agl::universe::MAX_STEPS;
    assert!(ask.element(&t, 3).is_some());
}

/// Criterion 5: the same answers whatever was asked before.
#[test]
fn determinism() {
    let u = Universe::new(9);
    let terms: Vec<L> = (1..=6).flat_map(|s| L::all(s, 0)).collect();
    let mut fresh = Vec::new();
    for t in &terms {
        fresh.push(Ask::new(&u).element(t, 3));
    }
    let mut ask = Ask::new(&u);
    let mut shared: Vec<_> = terms.iter().rev().map(|t| ask.element(t, 3)).collect();
    shared.reverse();
    assert_eq!(fresh, shared);
}

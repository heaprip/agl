//! A star for checking only (H75, `docs/impl/relations.md` §8): λ-terms,
//! put into formulas over E and P. The kernel does not know them; tests and
//! the example use them to see that gluing and abstraction behave as
//! functions where expected.
#![allow(dead_code)]

use agl::universe::F;

/// A λ-term with variables by the number of binders between them and their
/// own (de Bruijn).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum L {
    Var(usize),
    App(Box<L>, Box<L>),
    Lam(Box<L>),
}

impl L {
    pub fn app(a: L, b: L) -> L {
        L::App(Box::new(a), Box::new(b))
    }

    pub fn lam(a: L) -> L {
        L::Lam(Box::new(a))
    }

    pub fn size(&self) -> usize {
        match self {
            L::Var(_) => 1,
            L::App(a, b) => 1 + a.size() + b.size(),
            L::Lam(a) => 1 + a.size(),
        }
    }

    /// `self` with variable `k` replaced by `by` (closed terms only are put
    /// in, so nothing in `by` needs shifting).
    pub fn put(&self, k: usize, by: &L) -> L {
        match self {
            L::Var(i) if *i == k => by.clone(),
            L::Var(i) if *i > k => L::Var(i - 1),
            L::Var(i) => L::Var(*i),
            L::App(a, b) => L::app(a.put(k, by), b.put(k, by)),
            L::Lam(a) => L::lam(a.put(k + 1, by)),
        }
    }

    /// Every closed term of exactly `size` symbols, under `depth` binders.
    pub fn all(size: usize, depth: usize) -> Vec<L> {
        let mut out = Vec::new();
        if size == 1 {
            out.extend((0..depth).map(L::Var));
        }
        if size >= 2 {
            out.extend(L::all(size - 1, depth + 1).into_iter().map(L::lam));
        }
        for left in 1..size.saturating_sub(1) {
            for a in L::all(left, depth) {
                for b in L::all(size - 1 - left, depth) {
                    out.push(L::app(a.clone(), b));
                }
            }
        }
        out
    }

    /// The formula of membership in the term's element, of variable `out`:
    /// a variable is the set of its binder's token; application — b led to
    /// by a token of M whose set lies in N; abstraction — tokens whose set,
    /// put in for the variable, makes the body hold of where they lead.
    pub fn formula(&self, out: u8, binders: &mut Vec<u8>, next: &mut u8) -> F {
        let mut fresh = || {
            *next += 1;
            *next - 1
        };
        match self {
            L::Var(i) => F::E(out, binders[binders.len() - 1 - i]),
            L::App(m, n) => {
                let (t, c) = (fresh(), fresh());
                let fm = m.formula(t, binders, next);
                let fnn = n.formula(c, binders, next);
                F::Exists(
                    t,
                    Box::new(F::And(vec![
                        F::P(t, out),
                        fm,
                        F::Not(Box::new(F::Exists(
                            c,
                            Box::new(F::And(vec![F::E(c, t), F::Not(Box::new(fnn))])),
                        ))),
                    ])),
                )
            }
            L::Lam(m) => {
                let b = fresh();
                binders.push(out);
                let fm = m.formula(b, binders, next);
                binders.pop();
                F::Exists(b, Box::new(F::And(vec![F::P(out, b), fm])))
            }
        }
    }
}

impl std::fmt::Display for L {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            L::Var(i) => write!(f, "{i}"),
            L::App(a, b) => write!(f, "({a} {b})"),
            L::Lam(a) => write!(f, "λ{a}"),
        }
    }
}

/// The formula of a closed term, of variable 0.
pub fn of(t: &L) -> F {
    t.formula(0, &mut Vec::new(), &mut 1)
}

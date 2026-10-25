//! Laws with "exists" (`docs/impl/atlas.md` §12).
//!
//! Each "exists" becomes a new action: of the variables "for all" before
//! it, or a new constant if there are none (Skolem). The laws are then all
//! "for all", and completion gives their normal forms. A law with "exists"
//! follows when a witness is found: a term in the actions, of the
//! generators "for all" before it, making both sides one normal form. The
//! witness is the way to build what exists. Every action can be given
//! values in every model of the laws, so what is shown so is true; what is
//! not shown may still be true (the witness too large, or completion not
//! finished).

use crate::atlas::{Law, Term};
use crate::rewrite::{Expr, Theory};
use std::collections::BTreeSet;

/// Constants of laws with "exists" are numbered from this; generators
/// below it.
pub const CONSTANTS: u8 = 16;
/// The most symbols in a witness.
pub const MAX_WITNESS: u32 = 7;

pub struct Skolem {
    pub axioms: Vec<(Expr, Expr)>,
    /// Each new action and how many parts it takes; 0 is the operation.
    pub actions: Vec<(u8, usize)>,
    pub constants: Vec<u8>,
}

/// The laws with each "exists" replaced by a new action. Laws are taken in
/// the order of their text, so the numbering does not depend on the order
/// given.
pub fn skolemize(laws: &[&Law]) -> Skolem {
    let mut laws: Vec<&Law> = laws.to_vec();
    laws.sort_by_key(|l| l.to_string());
    // The first constant is some element: entities are not empty, so a
    // witness may be built when no other constant is there.
    let mut sk = Skolem {
        axioms: Vec::new(),
        actions: vec![(0, 2)],
        constants: vec![CONSTANTS],
    };
    for law in laws {
        let mut all: Vec<u8> = Vec::new();
        let mut instead: Vec<Option<Expr>> = vec![None; 8];
        for &(v, every) in &law.prefix {
            if every {
                all.push(v);
                continue;
            }
            let e = if all.is_empty() {
                let c = CONSTANTS + sk.constants.len() as u8;
                sk.constants.push(c);
                Expr::Con(c)
            } else {
                assert!(all.len() <= 2);
                let f = sk.actions.len() as u8;
                sk.actions.push((f, all.len()));
                Expr::App(f, all.iter().map(|&u| Expr::Var(u)).collect())
            };
            instead[v as usize] = Some(e);
        }
        sk.axioms
            .push((replace(&law.left, &instead), replace(&law.right, &instead)));
    }
    sk
}

fn replace(t: &Term, instead: &[Option<Expr>]) -> Expr {
    match t {
        Term::Var(v) => instead[*v as usize].clone().unwrap_or(Expr::Var(*v)),
        Term::Op(a, b) => Expr::App(0, vec![replace(a, instead), replace(b, instead)]),
    }
}

/// Normal forms of every term in the actions over the given atoms, up to
/// `MAX_WITNESS` symbols counted on normal forms; least first.
fn pool(th: &mut Theory, sk: &Skolem, atoms: &[u32]) -> Vec<u32> {
    let mut seen: BTreeSet<u32> = BTreeSet::new();
    let mut all: Vec<u32> = Vec::new();
    for &a in atoms {
        let n = th.normal(a);
        if seen.insert(n) {
            all.push(n);
        }
    }
    loop {
        let mut new = Vec::new();
        for &(f, arity) in &sk.actions {
            for &a in &all {
                let parts: Vec<Vec<u32>> = if arity == 1 {
                    vec![vec![a]]
                } else {
                    all.iter().map(|&b| vec![a, b]).collect()
                };
                for p in parts {
                    if p.iter().map(|&q| th.size(q)).sum::<u32>() + 1 > MAX_WITNESS {
                        continue;
                    }
                    let t = th.app(f, &p);
                    let n = th.normal(t);
                    if th.size(n) <= MAX_WITNESS && !seen.contains(&n) && !new.contains(&n) {
                        new.push(n);
                    }
                }
            }
        }
        if new.is_empty() || th.full() {
            all.sort_by_key(|&t| (th.size(t), th.text(t)));
            return all;
        }
        for n in new {
            seen.insert(n);
            all.push(n);
        }
    }
}

/// A witness for each "exists" of `law` in the theory, as text, if one
/// is found.
pub fn prove(th: &mut Theory, sk: &Skolem, law: &Law) -> Option<Vec<String>> {
    let mut env: Vec<u32> = vec![u32::MAX; 8];
    let mut gens = Vec::new();
    let mut pools: Vec<Option<Vec<u32>>> = vec![None; 4];
    let mut out = Vec::new();
    search(th, sk, law, 0, &mut env, &mut gens, &mut pools, &mut out).then_some(out)
}

#[allow(clippy::too_many_arguments)]
fn search(
    th: &mut Theory,
    sk: &Skolem,
    law: &Law,
    i: usize,
    env: &mut Vec<u32>,
    gens: &mut Vec<u32>,
    pools: &mut Vec<Option<Vec<u32>>>,
    out: &mut Vec<String>,
) -> bool {
    let Some(&(v, every)) = law.prefix.get(i) else {
        let l = build(th, &law.left, env);
        let r = build(th, &law.right, env);
        return th.normal(l) == th.normal(r);
    };
    if every {
        let g = th.con(gens.len() as u8);
        gens.push(g);
        env[v as usize] = g;
        let ok = search(th, sk, law, i + 1, env, gens, pools, out);
        gens.pop();
        return ok;
    }
    if pools[gens.len()].is_none() {
        let mut atoms = gens.clone();
        atoms.extend(sk.constants.iter().map(|&c| th.con(c)));
        pools[gens.len()] = Some(pool(th, sk, &atoms));
    }
    let candidates = pools[gens.len()].clone().unwrap();
    for w in candidates {
        if th.full() {
            return false;
        }
        env[v as usize] = w;
        out.push(format!("{} := {}", ["x", "y", "z"][v as usize], th.text(w)));
        if search(th, sk, law, i + 1, env, gens, pools, out) {
            return true;
        }
        out.pop();
    }
    false
}

fn build(th: &mut Theory, t: &Term, env: &[u32]) -> u32 {
    match t {
        Term::Var(v) => env[*v as usize],
        Term::Op(a, b) => {
            let (a, b) = (build(th, a, env), build(th, b, env));
            th.app(0, &[a, b])
        }
    }
}

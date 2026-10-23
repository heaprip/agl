//! Learning by theoretical generalization: looking for a general relation of a
//! given kind (a template) that accounts for labelled examples.
//!
//! The learner is given a learning task — a target relation and its examples —
//! and builds candidates only from relations it already has. A candidate must
//! account for every training example; it is then judged on held-out ones,
//! which it never saw. The learned rules are proposals: they are returned, not
//! added to the program.
//!
//! Template `subset`: an entity has the property when everything it is
//! R-related to is P — `target(s) ⇐ ∀x (R(s, x) → P(x))`, and the negation when
//! some R-related x is not P. Counting aggregates express the quantifier.

use std::collections::{BTreeMap, BTreeSet};

use crate::check;
use crate::eval::{self, Outcome};
use crate::model::*;

/// How many hypotheses to return.
const TOP: usize = 5;

#[derive(Clone, Debug)]
pub struct Hypothesis {
    /// `∀x R(s, x) → P(x)` in words.
    pub reading: String,
    pub rules: Vec<Rule>,
    /// Met and total, on training and on held-out examples.
    pub train: (usize, usize),
    pub heldout: (usize, usize),
}

struct Example<'a> {
    query: &'a Query,
    plane: Plane,
}

pub fn learn(prog: &Program, target: &str) -> (Vec<Hypothesis>, Vec<String>) {
    let mut base = prog.clone();
    base.rules.retain(|r| r.head.rel != target);
    let examples: Vec<Example> = prog
        .queries
        .iter()
        .filter(|q| q.atom.rel == target && matches!(q.expect, Some(Verdict::Yes | Verdict::No)))
        .map(|q| Example {
            query: q,
            plane: check::effective_plane(&base, q),
        })
        .collect();
    let (train, held): (Vec<&Example>, Vec<&Example>) =
        examples.iter().partition(|e| !e.query.heldout);
    if train.is_empty() {
        return (vec![], vec![format!("no training examples for `{target}`")]);
    }
    let Some(role_t) = single_role(&examples) else {
        return (
            vec![],
            vec![format!(
                "examples of `{target}` must have exactly one role, the same in all"
            )],
        );
    };
    let entities: BTreeSet<String> = examples
        .iter()
        .filter_map(|e| value(&e.query.atom, &role_t))
        .collect();

    // The relations the learner already knows, as they hold in training planes.
    let mut outs: BTreeMap<String, Outcome> = BTreeMap::new();
    for e in &train {
        outs.entry(plane_to_string(&e.plane))
            .or_insert_with(|| eval::evaluate(&base, &e.plane));
    }
    let known = vocabulary(outs.values(), target);

    let Some((d_rel, d_role)) = domain(&base, &entities) else {
        return (
            vec![],
            vec!["no fact relation covers every example entity".into()],
        );
    };

    let mut found = Vec::new();
    let mut considered = 0;
    for ((r_rel, r_s, r_x), x_values) in &known.pairs {
        if !known
            .values(r_rel, r_s)
            .iter()
            .any(|v| entities.contains(v))
        {
            continue;
        }
        for ((p_rel, p_role), p_values) in &known.unary {
            if p_rel == r_rel || p_values.is_disjoint(x_values) {
                continue;
            }
            considered += 1;
            let rules = subset_rules(
                target,
                &role_t,
                (&d_rel, &d_role),
                (r_rel, r_s, r_x),
                (p_rel, p_role),
            );
            let mut p = base.clone();
            p.rules.extend(rules.iter().cloned());
            let train_met = met(&p, &train);
            if train_met < train.len() {
                continue;
            }
            found.push(Hypothesis {
                reading: format!("{target}({role_t}: s) ⇐ every x with {r_rel}({r_s}: s, {r_x}: x) has {p_rel}({p_role}: x)"),
                rules,
                train: (train_met, train.len()),
                heldout: (met(&p, &held), held.len()),
            });
        }
    }
    found.sort_by(|a, b| (b.heldout.0, &a.reading).cmp(&(a.heldout.0, &b.reading)));
    let fitting = found.len();
    found.truncate(TOP);
    let mut notes = vec![format!(
        "{considered} candidates of template `subset` over the known vocabulary; {fitting} account for every training example"
    )];
    if found.is_empty() {
        notes.push(format!(
            "no `subset` hypothesis accounts for every training example of `{target}`"
        ));
    }
    (found, notes)
}

fn single_role(examples: &[Example]) -> Option<String> {
    let roles: BTreeSet<Vec<String>> = examples
        .iter()
        .map(|e| e.query.atom.args.iter().map(|(r, _)| r.clone()).collect())
        .collect();
    match roles.into_iter().collect::<Vec<_>>().as_slice() {
        [one] if one.len() == 1 => Some(one[0].clone()),
        _ => None,
    }
}

fn value(a: &Atom, role: &str) -> Option<String> {
    a.args
        .iter()
        .find(|(r, _)| r == role)
        .map(|(_, t)| t.to_string())
}

/// Known relations: binary role pairs with the values of the second role, and
/// single roles with their values.
#[derive(Default)]
struct Vocabulary {
    pairs: BTreeMap<(String, String, String), BTreeSet<String>>,
    unary: BTreeMap<(String, String), BTreeSet<String>>,
}

impl Vocabulary {
    fn values(&self, rel: &str, role: &str) -> BTreeSet<String> {
        self.unary
            .get(&(rel.to_string(), role.to_string()))
            .cloned()
            .unwrap_or_default()
    }
}

fn vocabulary<'a>(outs: impl Iterator<Item = &'a Outcome>, target: &str) -> Vocabulary {
    let mut v = Vocabulary::default();
    for out in outs {
        for (atom, _) in out.db.values() {
            if atom.neg || atom.rel == target || atom.rel == "situated" {
                continue;
            }
            for (ra, ta) in &atom.args {
                v.unary
                    .entry((atom.rel.clone(), ra.clone()))
                    .or_default()
                    .insert(ta.to_string());
                for (rb, tb) in &atom.args {
                    if ra != rb {
                        v.pairs
                            .entry((atom.rel.clone(), ra.clone(), rb.clone()))
                            .or_default()
                            .insert(tb.to_string());
                    }
                }
            }
        }
    }
    v
}

/// The fact relation and role whose values include every example entity, the
/// narrowest such; it ranges the learned rule over the right kind of thing.
fn domain(prog: &Program, entities: &BTreeSet<String>) -> Option<(String, String)> {
    let mut sets: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    for f in &prog.facts {
        for (role, t) in &f.atom.args {
            sets.entry((f.atom.rel.clone(), role.clone()))
                .or_default()
                .insert(t.to_string());
        }
    }
    sets.into_iter()
        .filter(|(_, vals)| entities.is_subset(vals))
        .min_by(|(ka, a), (kb, b)| (a.len(), ka).cmp(&(b.len(), kb)))
        .map(|(k, _)| k)
}

fn var(v: &str) -> Term {
    Term::Var(v.to_string())
}

fn atom(rel: &str, args: &[(&str, &str)]) -> Atom {
    Atom::new(
        rel.to_string(),
        args.iter().map(|(r, v)| (r.to_string(), var(v))).collect(),
        false,
    )
}

fn subset_rules(
    target: &str,
    role_t: &str,
    (d_rel, d_role): (&str, &str),
    (r_rel, r_s, r_x): (&str, &str, &str),
    (p_rel, p_role): (&str, &str),
) -> Vec<Rule> {
    let d = Lit::Atom(atom(d_rel, &[(d_role, "s")]));
    let r = atom(r_rel, &[(r_s, "s"), (r_x, "x")]);
    let p = atom(p_rel, &[(p_role, "x")]);
    let count = |name: &str, over: Vec<Atom>| Lit::Agg {
        var: name.to_string(),
        func: AggFn::Count,
        expr: Expr::Term(var("x")),
        over,
    };
    let eq = |a: &str, b: Expr| Lit::Cmp(Expr::Term(var(a)), CmpOp::Eq, b);
    vec![
        Rule {
            id: "learned_pos".into(),
            head: atom(target, &[(role_t, "s")]),
            body: vec![
                d.clone(),
                count("c", vec![r.clone()]),
                count("a", vec![r.clone(), p.clone()]),
                eq("c", Expr::Term(var("a"))),
            ],
            strength: Strength::Defeasible,
            plane: Plane::new(),
            line: 0,
        },
        Rule {
            id: "learned_neg".into(),
            head: atom(target, &[(role_t, "s")]).complement(),
            body: vec![
                d,
                Lit::Atom(r),
                count("k", vec![p]),
                eq("k", Expr::Term(Term::Num(0.0, crate::units::Dim::NONE))),
            ],
            strength: Strength::Defeasible,
            plane: Plane::new(),
            line: 0,
        },
    ]
}

/// How many examples get their expected verdict; one evaluation per plane.
fn met(prog: &Program, examples: &[&Example]) -> usize {
    let mut outs: BTreeMap<String, Outcome> = BTreeMap::new();
    examples
        .iter()
        .filter(|e| {
            let out = outs
                .entry(plane_to_string(&e.plane))
                .or_insert_with(|| eval::evaluate(prog, &e.plane));
            Some(verdict(out, &e.query.atom)) == e.query.expect
        })
        .count()
}

fn verdict(out: &Outcome, a: &Atom) -> Verdict {
    let pos = if a.neg { a.complement() } else { a.clone() };
    if out.conflicts.contains_key(&pos.key()) {
        Verdict::Conflict
    } else if out.db.contains_key(&a.key()) {
        Verdict::Yes
    } else if out.db.contains_key(&a.complement().key()) {
        Verdict::No
    } else {
        Verdict::Unknown
    }
}

/// Canonical text of the learning result.
pub fn render(hs: &[Hypothesis], notes: &[String]) -> String {
    let mut s = String::new();
    for (i, h) in hs.iter().enumerate() {
        s.push_str(&format!(
            "hypothesis {}: {}\n  training {}/{}, held-out {}/{}\n",
            i + 1,
            h.reading,
            h.train.0,
            h.train.1,
            h.heldout.0,
            h.heldout.1
        ));
        for r in &h.rules {
            s.push_str(&format!("  {}\n", r.to_source()));
        }
    }
    for n in notes {
        s.push_str(&format!("note: {n}\n"));
    }
    s
}

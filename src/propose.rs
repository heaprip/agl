//! Reflection, stage R2: proposals.
//!
//! From the diagnosis, generates small structural changes, applies each to a
//! copy of the program and keeps those that make more expectations come true
//! while making none worse. Nothing is applied to the program itself: the
//! result is a ranked list of patches in the case notation, for the author.
//! Candidates are enumerated and ranked in canonical order, so proposals are
//! deterministic and independent of statement order.

use std::collections::BTreeSet;

use crate::check::{self, Report};
use crate::model::*;
use crate::reflect::{self, Kind};

/// Children sets larger than this are not enumerated for intermediate values.
const MAX_CHILDREN: usize = 10;
/// How many proposals to return.
const TOP: usize = 5;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    /// Declare `winner` defeats `loser`. `by_body`: the winner's body contains
    /// every atom pattern of the loser's, so it is the more specific rule.
    Defeats {
        winner: String,
        loser: String,
        by_body: bool,
    },
    /// Move a rule into a narrower existing plane.
    MoveRule { rule: String, to: Plane },
    /// Insert value `name` between `parent` and `children` on `axis`, and move
    /// `rule` there: an intermediate plane.
    Intermediate {
        axis: String,
        parent: String,
        children: Vec<String>,
        name: String,
        rule: String,
    },
}

impl Op {
    fn cost(&self) -> usize {
        match self {
            Op::Defeats { .. } | Op::MoveRule { .. } => 1,
            Op::Intermediate { .. } => 2,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Proposal {
    pub op: Op,
    /// Expectations met before and after.
    pub before: usize,
    pub after: usize,
    /// Lines of expectations still unmet after the change.
    pub remaining: Vec<usize>,
    pub patch: String,
}

pub fn propose(prog: &Program) -> (Vec<Proposal>, Vec<String>) {
    let base = check::run(prog);
    let before = met(&base);
    if base.failed_queries().next().is_none() {
        return (vec![], vec![]);
    }
    let diags = reflect::diagnose(prog);
    let mut suspects: BTreeSet<String> = BTreeSet::new();
    let mut pairs: BTreeSet<(String, String)> = BTreeSet::new();
    for d in &diags {
        if matches!(d.kind, Kind::WrongAnswer | Kind::Conflict) {
            suspects.extend(d.support.iter().cloned());
        }
    }
    for c in &base.conflicts {
        for p in &c.conflict.sources_pos {
            for n in &c.conflict.sources_neg {
                if is_rule(prog, p) && is_rule(prog, n) && p != n {
                    pairs.insert((p.clone(), n.clone()));
                }
            }
        }
    }
    let failing_contexts: BTreeSet<Plane> = base
        .failed_queries()
        .map(|q| q.query.plane.clone())
        .collect();

    let mut candidates: BTreeSet<Op> = BTreeSet::new();
    for (p, n) in &pairs {
        for (w, l) in [(p, n), (n, p)] {
            if !prog.defeats.contains(&(w.clone(), l.clone())) {
                candidates.insert(Op::Defeats {
                    winner: w.clone(),
                    loser: l.clone(),
                    by_body: body_covers(rule(prog, w), rule(prog, l)),
                });
            }
        }
    }
    for id in &suspects {
        let r = rule(prog, id);
        let mut targets: BTreeSet<Plane> = failing_contexts.clone();
        targets.extend(prog.planes.values().cloned());
        for t in targets {
            if prog.axes.strictly_within(&t, &r.plane) {
                candidates.insert(Op::MoveRule {
                    rule: id.clone(),
                    to: t,
                });
            }
        }
        for (axis, value) in &r.plane {
            let children = prog.axes.children(axis, value);
            if children.len() < 3 || children.len() > MAX_CHILDREN {
                continue;
            }
            for set in subsets(&children) {
                if set.len() < 2 || set.len() == children.len() {
                    continue;
                }
                let name = format!("{value}_{}", set.join("_"));
                candidates.insert(Op::Intermediate {
                    axis: axis.clone(),
                    parent: value.clone(),
                    children: set,
                    name,
                    rule: id.clone(),
                });
            }
        }
    }

    let mut accepted: Vec<Proposal> = Vec::new();
    for op in candidates {
        let Some(changed) = apply(prog, &op) else {
            continue;
        };
        let report = check::run(&changed);
        if report.has_errors() || worse(&base, &report) {
            continue;
        }
        let after = met(&report);
        let fewer_conflicts = report.conflicts.len() < base.conflicts.len();
        if after > before || (after == before && fewer_conflicts) {
            let remaining = report.failed_queries().map(|q| q.query.line).collect();
            let patch = patch(prog, &op);
            accepted.push(Proposal {
                op,
                before,
                after,
                remaining,
                patch,
            });
        }
    }
    accepted.sort_by(|a, b| (b.after, a.op.cost(), &a.op).cmp(&(a.after, b.op.cost(), &b.op)));
    accepted.truncate(TOP);

    let mut notes = Vec::new();
    if accepted.iter().all(|p| !p.remaining.is_empty()) {
        notes.extend(new_axis_hint(prog, &base));
    }
    (accepted, notes)
}

fn met(r: &Report) -> usize {
    r.queries
        .iter()
        .filter(|q| q.query.expect == Some(q.verdict))
        .count()
}

/// A change is worse if a met expectation fails, or an unmet one gets the
/// opposite definite answer.
fn worse(base: &Report, now: &Report) -> bool {
    base.queries
        .iter()
        .zip(&now.queries)
        .any(|(b, n)| match b.query.expect {
            Some(e) if b.verdict == e => n.verdict != e,
            Some(Verdict::Yes) => n.verdict == Verdict::No,
            Some(Verdict::No) => n.verdict == Verdict::Yes,
            _ => false,
        })
}

fn is_rule(prog: &Program, id: &str) -> bool {
    prog.rules.iter().any(|r| r.id == id)
}

fn rule<'a>(prog: &'a Program, id: &str) -> &'a Rule {
    prog.rules
        .iter()
        .find(|r| r.id == id)
        .expect("candidate rules exist")
}

/// Every atom pattern of `loser`'s body (relation, sign and roles) occurs in
/// `winner`'s body: the winner applies in a narrower set of cases.
fn body_covers(winner: &Rule, loser: &Rule) -> bool {
    let shape = |a: &Atom| {
        (
            a.rel.clone(),
            a.neg,
            a.args.iter().map(|(r, _)| r.clone()).collect::<Vec<_>>(),
        )
    };
    let atoms = |r: &Rule| -> Vec<(String, bool, Vec<String>)> {
        r.body
            .iter()
            .filter_map(|l| {
                if let Lit::Atom(a) = l {
                    Some(shape(a))
                } else {
                    None
                }
            })
            .collect()
    };
    let (w, l) = (atoms(winner), atoms(loser));
    w.len() > l.len() && l.iter().all(|x| w.contains(x))
}

fn subsets(xs: &[String]) -> Vec<Vec<String>> {
    let n = xs.len();
    let mut out: Vec<Vec<String>> = (1u32..(1 << n))
        .map(|mask| {
            (0..n)
                .filter(|i| mask & (1 << i) != 0)
                .map(|i| xs[i].clone())
                .collect()
        })
        .collect();
    out.sort_by(|a: &Vec<String>, b| (a.len(), a).cmp(&(b.len(), b)));
    out
}

pub fn apply(prog: &Program, op: &Op) -> Option<Program> {
    let mut p = prog.clone();
    match op {
        Op::Defeats { winner, loser, .. } => {
            p.defeats.insert((winner.clone(), loser.clone()));
        }
        Op::MoveRule { rule, to } => {
            p.rules.iter_mut().find(|r| &r.id == rule)?.plane = to.clone();
        }
        Op::Intermediate {
            axis,
            parent,
            children,
            name,
            rule,
        } => {
            if p.axes.has_value(axis, name) {
                return None;
            }
            p.axes.declare_value(axis, name, Some(parent)).ok()?;
            for c in children {
                p.axes.reparent(axis, c, name).ok()?;
            }
            p.rules
                .iter_mut()
                .find(|r| &r.id == rule)?
                .plane
                .insert(axis.clone(), name.clone());
        }
    }
    Some(p)
}

/// The change in the case notation: lines to remove (`-`) and add (`+`).
fn patch(prog: &Program, op: &Op) -> String {
    let mut lines = Vec::new();
    match op {
        Op::Defeats {
            winner,
            loser,
            by_body,
        } => {
            lines.push(format!("+ defeats {winner} {loser}"));
            if *by_body {
                lines.push(format!("  # `{winner}` covers every condition of `{loser}` and adds more: it is the more specific rule"));
            }
        }
        Op::MoveRule { rule: id, to } => {
            let old = rule(prog, id);
            let mut new = old.clone();
            new.plane = to.clone();
            lines.push(format!("- {}", old.to_source()));
            lines.push(format!("+ {}", new.to_source()));
        }
        Op::Intermediate {
            axis,
            parent,
            children,
            name,
            rule: id,
        } => {
            lines.push(format!("+ value {axis} {name} in {parent}"));
            for c in children {
                lines.push(format!("- value {axis} {c} in {parent}"));
                lines.push(format!("+ value {axis} {c} in {name}"));
            }
            let old = rule(prog, id);
            let mut new = old.clone();
            new.plane.insert(axis.clone(), name.clone());
            lines.push(format!("- {}", old.to_source()));
            lines.push(format!("+ {}", new.to_source()));
            lines.push(format!(
                "  # `{name}` is an intermediate plane: rename it to say what unites {}",
                children.join(", ")
            ));
        }
    }
    lines.join("\n")
}

/// When failing contexts that want the same answer sit under different
/// parents on an axis, no intermediate value can group them: say so.
fn new_axis_hint(prog: &Program, base: &Report) -> Vec<String> {
    let mut by_answer: std::collections::BTreeMap<(String, String), BTreeSet<(String, String)>> =
        std::collections::BTreeMap::new();
    for q in base.failed_queries() {
        let Some(e) = q.query.expect else { continue };
        for (axis, value) in &q.query.plane {
            by_answer
                .entry((q.query.atom.key(), e.to_string()))
                .or_default()
                .insert((axis.clone(), value.clone()));
        }
    }
    let mut notes = Vec::new();
    for ((atom, e), places) in by_answer {
        let mut parents: BTreeSet<(String, Option<String>)> = BTreeSet::new();
        for (axis, value) in &places {
            parents.insert((axis.clone(), prog.axes.parent(axis, value)));
        }
        let axes: BTreeSet<&String> = parents.iter().map(|(a, _)| a).collect();
        if places.len() >= 2 && axes.len() == 1 && parents.len() > 1 {
            let values: Vec<String> = places.iter().map(|(_, v)| v.clone()).collect();
            notes.push(format!(
                "{atom} is expected {e} in {} which have different parents: no intermediate value groups them; a new axis may",
                values.join(", ")
            ));
        }
    }
    notes
}

/// Canonical text of a proposal list.
pub fn render(ps: &[Proposal], notes: &[String]) -> String {
    let mut s = String::new();
    for (i, p) in ps.iter().enumerate() {
        let rem: Vec<String> = p.remaining.iter().map(|l| l.to_string()).collect();
        s.push_str(&format!(
            "proposal {}: expectations met {} -> {}{}\n{}\n",
            i + 1,
            p.before,
            p.after,
            if rem.is_empty() {
                String::new()
            } else {
                format!(", still unmet on lines {}", rem.join(", "))
            },
            p.patch
        ));
    }
    for n in notes {
        s.push_str(&format!("note: {n}\n"));
    }
    s
}

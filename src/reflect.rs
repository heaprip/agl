//! Reflection, stage R1: diagnosis.
//!
//! Looks at the program's own results and says what is responsible when an
//! expectation fails or a conflict shows. It changes nothing: removing a rule
//! here is a probe ("what if this rule were not there?"), not a proposal.
//! Targets are failed expectations and reported conflicts; disagreement
//! between disjoint planes, such as moral branches, never reaches here.
//! Everything is enumerated in canonical order, so the diagnosis is
//! deterministic and independent of statement order.

use std::collections::BTreeSet;

use crate::check::{self, FoundConflict};
use crate::eval::{self, Outcome};
use crate::model::*;

/// Probes stop at this many rules in a culprit set.
const MAX_CULPRIT: usize = 2;
/// Support larger than this is not searched for culprits.
const MAX_SUPPORT: usize = 12;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Expected one verdict, derived another.
    WrongAnswer,
    /// Expected an answer, derived none.
    Missing,
    /// A conflict the planes do not settle.
    Conflict,
}

#[derive(Clone, Debug)]
pub struct Diagnosis {
    pub kind: Kind,
    pub target: String,
    /// Rules the result rests on.
    pub support: Vec<String>,
    /// Minimal sets of rules whose absence would settle the target without
    /// breaking any expectation that holds now.
    pub culprits: Vec<Vec<String>>,
    pub notes: Vec<String>,
}

pub fn diagnose(prog: &Program) -> Vec<Diagnosis> {
    let report = check::run(prog);
    let passing: Vec<usize> = report
        .queries
        .iter()
        .enumerate()
        .filter(|(_, q)| q.query.expect == Some(q.verdict))
        .map(|(i, _)| i)
        .collect();
    let mut out = Vec::new();
    for r in report.failed_queries() {
        let expect = r.query.expect.expect("failed queries have an expectation");
        out.push(match r.verdict {
            Verdict::Unknown | Verdict::Gap if matches!(expect, Verdict::Yes | Verdict::No) => {
                missing(prog, &r.query, expect)
            }
            _ => wrong(prog, &r.query, expect, r.verdict, &passing),
        });
    }
    for c in &report.conflicts {
        out.push(conflict(prog, c, &passing));
    }
    out
}

fn target_name(q: &Query) -> String {
    format!("{} @ {}", q.atom, plane_to_string(&q.plane))
}

/// Every rule any derivation of `key` rests on, transitively.
fn support(out: &Outcome, key: &str) -> BTreeSet<String> {
    let mut rules = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![key.to_string()];
    while let Some(k) = stack.pop() {
        if !seen.insert(k.clone()) {
            continue;
        }
        let Some((_, derivs)) = out.db.get(&k) else {
            continue;
        };
        for d in derivs {
            if !d.is_fact {
                rules.insert(d.source.to_string());
            }
            stack.extend(d.premises.iter().cloned());
        }
    }
    rules
}

fn without(prog: &Program, removed: &[String]) -> Program {
    let mut p = prog.clone();
    p.rules.retain(|r| !removed.iter().any(|x| r.id == *x));
    p
}

/// Minimal removal sets, smallest first: a set qualifies if `settled` holds
/// without it and every currently passing expectation still passes.
fn culprits(
    prog: &Program,
    support: &BTreeSet<String>,
    passing: &[usize],
    settled: impl Fn(&Program) -> bool,
) -> (Vec<Vec<String>>, Option<String>) {
    let candidates: Vec<String> = support.iter().cloned().collect();
    if candidates.len() > MAX_SUPPORT {
        return (
            vec![],
            Some(format!(
                "support of {} rules is too large to probe",
                candidates.len()
            )),
        );
    }
    // Lines of expectations that `p` makes worse: a passing one that fails, or
    // a failing one that now gets the opposite definite answer.
    let opposite = |v: Verdict| match v {
        Verdict::Yes => Some(Verdict::No),
        Verdict::No => Some(Verdict::Yes),
        _ => None,
    };
    let broken = |p: &Program| -> Vec<usize> {
        let r = check::run(p);
        r.queries
            .iter()
            .enumerate()
            .filter(|(i, q)| {
                let Some(e) = q.query.expect else {
                    return false;
                };
                if passing.contains(i) {
                    e != q.verdict
                } else {
                    opposite(e) == Some(q.verdict)
                }
            })
            .map(|(_, q)| q.query.line)
            .collect()
    };
    let mut found: Vec<Vec<String>> = Vec::new();
    let mut blocked: Vec<(Vec<String>, Vec<usize>)> = Vec::new();
    for size in 1..=MAX_CULPRIT.min(candidates.len()) {
        for set in combinations(&candidates, size) {
            if found.iter().any(|f| f.iter().all(|x| set.contains(x))) {
                continue;
            }
            let p = without(prog, &set);
            if !settled(&p) {
                continue;
            }
            let lines = broken(&p);
            if lines.is_empty() {
                found.push(set);
            } else if blocked.len() < 3
                && !blocked
                    .iter()
                    .any(|(b, _)| b.iter().all(|x| set.contains(x)))
            {
                blocked.push((set, lines));
            }
        }
        if !found.is_empty() {
            break;
        }
    }
    let note = (found.is_empty() && !blocked.is_empty()).then(|| {
        let parts: Vec<String> = blocked
            .iter()
            .map(|(set, lines)| {
                let lines: Vec<String> = lines.iter().map(|l| l.to_string()).collect();
                format!(
                    "without [{}] it settles, but expectations on lines {} fail",
                    set.join(", "),
                    lines.join(", ")
                )
            })
            .collect();
        format!("no removal keeps every expectation: {}", parts.join("; "))
    });
    (found, note)
}

fn combinations(xs: &[String], k: usize) -> Vec<Vec<String>> {
    fn rec(
        xs: &[String],
        k: usize,
        start: usize,
        cur: &mut Vec<String>,
        out: &mut Vec<Vec<String>>,
    ) {
        if cur.len() == k {
            out.push(cur.clone());
            return;
        }
        for i in start..xs.len() {
            cur.push(xs[i].clone());
            rec(xs, k, i + 1, cur, out);
            cur.pop();
        }
    }
    let mut out = Vec::new();
    rec(xs, k, 0, &mut Vec::new(), &mut out);
    out
}

fn verdict_of(prog: &Program, q: &Query) -> Verdict {
    let mut p = without(prog, &[]);
    p.queries = vec![q.clone()];
    check::run(&p).queries[0].verdict
}

fn wrong(prog: &Program, q: &Query, expect: Verdict, got: Verdict, passing: &[usize]) -> Diagnosis {
    let out = eval::evaluate(prog, &check::effective_plane(prog, q));
    let key = match got {
        Verdict::No => q.atom.complement().key(),
        _ => q.atom.key(),
    };
    let mut sup = support(&out, &key);
    if got == Verdict::Conflict {
        sup.extend(support(&out, &q.atom.complement().key()));
        let pos = if q.atom.neg {
            q.atom.complement().key()
        } else {
            q.atom.key()
        };
        if let Some(c) = out.conflicts.get(&pos) {
            sup.extend(
                c.sources_pos
                    .iter()
                    .chain(&c.sources_neg)
                    .filter(|s| prog.rules.iter().any(|r| &r.id == *s))
                    .cloned(),
            );
        }
    }
    let (found, note) = culprits(prog, &sup, passing, |p| verdict_of(p, q) == expect);
    let mut notes = vec![format!("expected {expect}, derived {got}")];
    notes.extend(note);
    notes.extend(plane_notes(prog, &sup, &q.plane));
    Diagnosis {
        kind: Kind::WrongAnswer,
        target: target_name(q),
        support: sup.into_iter().collect(),
        culprits: found,
        notes,
    }
}

/// How a rule's plane stands to the context it was asked in.
fn relation(prog: &Program, rule_plane: &Plane, ctx: &Plane) -> &'static str {
    if prog.axes.plane_within(ctx, rule_plane) {
        if prog.axes.plane_within(rule_plane, ctx) {
            "the context itself"
        } else {
            "contains the context"
        }
    } else if prog.axes.plane_meet(ctx, rule_plane).is_none() {
        "disjoint from the context"
    } else if prog.axes.plane_within(rule_plane, ctx) {
        "nested inside the context, not visible from it"
    } else {
        "overlaps the context, not visible from it"
    }
}

fn plane_notes(prog: &Program, rules: &BTreeSet<String>, ctx: &Plane) -> Vec<String> {
    // In rule-id order, not program order: the diagnosis must not depend on it.
    let mut in_rules: Vec<&Rule> = prog
        .rules
        .iter()
        .filter(|r| rules.contains(r.id.as_str()))
        .collect();
    in_rules.sort_by(|a, b| a.id.cmp(&b.id));
    in_rules
        .into_iter()
        .map(|r| {
            format!(
                "rule `{}` holds in {}: {}",
                r.id,
                plane_to_string(&r.plane),
                relation(prog, &r.plane, ctx)
            )
        })
        .collect()
}

fn missing(prog: &Program, q: &Query, expect: Verdict) -> Diagnosis {
    let want = if expect == Verdict::No {
        q.atom.complement()
    } else {
        q.atom.clone()
    };
    let out = eval::evaluate(prog, &check::effective_plane(prog, q));
    let mut notes = vec![format!("expected {expect}, nothing derives {want}")];
    let mut sup = BTreeSet::new();
    let mut heads: Vec<&Rule> = prog
        .rules
        .iter()
        .filter(|r| r.head.rel == want.rel && r.head.neg == want.neg)
        .collect();
    heads.sort_by(|a, b| a.id.cmp(&b.id));
    for r in heads {
        sup.insert(r.id.to_string());
        let rel = relation(prog, &r.plane, &q.plane);
        if !prog.axes.plane_within(&q.plane, &r.plane) {
            notes.push(format!(
                "rule `{}` concludes {} but holds in {}: {rel}",
                r.id,
                r.head.rel,
                plane_to_string(&r.plane)
            ));
            continue;
        }
        notes.push(format!(
            "rule `{}` is visible; {}",
            r.id,
            first_failing(r, &want, &out)
        ));
    }
    if sup.is_empty() {
        notes.push(format!(
            "no rule concludes `{}{}`",
            if want.neg { "¬" } else { "" },
            want.rel
        ));
    }
    let mut facts: Vec<String> = prog
        .facts
        .iter()
        .filter(|f| f.atom == want && !prog.axes.plane_within(&q.plane, &f.plane))
        .map(|f| {
            format!(
                "fact `{}` states it in {}: {}",
                f.id,
                plane_to_string(&f.plane),
                relation(prog, &f.plane, &q.plane)
            )
        })
        .collect();
    facts.sort();
    notes.extend(facts);
    Diagnosis {
        kind: Kind::Missing,
        target: target_name(q),
        support: sup.into_iter().collect(),
        culprits: vec![],
        notes,
    }
}

/// The first body atom that no visible atom matches once the head is unified
/// with the wanted atom; comparisons and aggregates are reported as such.
fn first_failing(r: &Rule, want: &Atom, out: &Outcome) -> String {
    let mut binding: std::collections::BTreeMap<String, Term> = std::collections::BTreeMap::new();
    for (role, t) in &r.head.args {
        if let (Term::Var(v), Some((_, g))) = (t, want.args.iter().find(|(rr, _)| rr == role)) {
            binding.insert(v.clone(), g.clone());
        }
    }
    for lit in &r.body {
        match lit {
            Lit::Atom(a) => {
                let pat = eval::subst(a, &binding);
                let any = out.db.values().any(|(g, _)| {
                    g.rel == pat.rel
                        && g.neg == pat.neg
                        && pat.args.iter().all(|(role, t)| {
                            matches!(t, Term::Var(_))
                                || g.args.iter().any(|(rr, gt)| rr == role && gt == t)
                        })
                });
                if !any {
                    return format!("no visible atom matches `{pat}`");
                }
            }
            Lit::Cmp(..) | Lit::Agg { .. } => {}
        }
    }
    "its atoms match, so a comparison, an aggregate or a defeat stops it".into()
}

fn conflict(prog: &Program, c: &FoundConflict, passing: &[usize]) -> Diagnosis {
    let rules: BTreeSet<String> = c
        .conflict
        .sources_pos
        .iter()
        .chain(&c.conflict.sources_neg)
        .filter(|s| prog.rules.iter().any(|r| &r.id == *s))
        .cloned()
        .collect();
    let out = eval::evaluate(prog, &c.context);
    let mut sup = rules.clone();
    if let Some(k) = out.db.keys().find(|k| **k == c.conflict.positive) {
        sup.extend(support(&out, k));
    }
    let ctx = c.context.clone();
    let positive = c.conflict.positive.clone();
    let (found, note) = culprits(prog, &sup, passing, |p| {
        !eval::evaluate(p, &ctx).conflicts.contains_key(&positive)
    });
    let mut notes = vec![format!(
        "{:?} conflict in {}: for [{}] against [{}]",
        c.conflict.kind,
        plane_to_string(&c.context),
        c.conflict.sources_pos.join(", "),
        c.conflict.sources_neg.join(", ")
    )];
    notes.extend(note);
    notes.extend(plane_notes(prog, &rules, &c.context));
    let in_rules: Vec<&Rule> = prog
        .rules
        .iter()
        .filter(|r| rules.contains(r.id.as_str()))
        .collect();
    if in_rules.len() >= 2 && in_rules.windows(2).all(|w| w[0].plane == w[1].plane) {
        notes.push("the rules share one plane: no specificity can separate them".into());
    }
    Diagnosis {
        kind: Kind::Conflict,
        target: c.conflict.positive.clone(),
        support: sup.into_iter().collect(),
        culprits: found,
        notes,
    }
}

/// Canonical text of a diagnosis list.
pub fn render(ds: &[Diagnosis]) -> String {
    let mut parts: Vec<String> = ds
        .iter()
        .map(|d| {
            let mut s = format!("{:?}: {}\n", d.kind, d.target);
            s.push_str(&format!("  support: [{}]\n", d.support.join(", ")));
            for c in &d.culprits {
                s.push_str(&format!("  culprit: [{}]\n", c.join(", ")));
            }
            for n in &d.notes {
                s.push_str(&format!("  - {n}\n"));
            }
            s
        })
        .collect();
    parts.sort();
    parts.join("")
}

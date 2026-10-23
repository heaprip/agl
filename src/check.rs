//! Whole-program check: lint, contradiction scan over plane intersections,
//! and queries with their expected verdicts.

use std::collections::{BTreeMap, BTreeSet};

use crate::eval::{self, ConflictKind, Outcome};
use crate::lint::{self, Diag, Level};
use crate::model::*;

#[derive(Debug)]
pub struct QueryResult {
    pub query: Query,
    pub verdict: Verdict,
    pub explanation: String,
}

#[derive(Debug)]
pub struct FoundConflict {
    pub context: Plane,
    pub conflict: eval::Conflict,
}

#[derive(Debug)]
pub struct Report {
    pub diags: Vec<Diag>,
    /// Evaluation errors, such as dimension mismatches, from any context.
    pub errors: Vec<String>,
    pub conflicts: Vec<FoundConflict>,
    pub queries: Vec<QueryResult>,
}

impl Report {
    pub fn failed_queries(&self) -> impl Iterator<Item = &QueryResult> {
        self.queries
            .iter()
            .filter(|q| q.query.expect.is_some_and(|e| e != q.verdict))
    }

    pub fn has_errors(&self) -> bool {
        self.diags.iter().any(|d| d.level == Level::Error) || !self.errors.is_empty()
    }
}

pub fn run(prog: &Program) -> Report {
    let diags = lint::lint(prog);
    let (conflicts, mut errors) = scan_conflicts(prog);
    let queries: Vec<QueryResult> = prog
        .queries
        .iter()
        .map(|q| answer(prog, q, &mut errors))
        .collect();
    Report {
        diags,
        errors: errors.into_iter().collect(),
        conflicts,
        queries,
    }
}

/// Contexts worth checking: every plane in use, and every non-empty meet of two.
fn contexts(prog: &Program) -> Vec<Plane> {
    fn push(planes: &mut Vec<Plane>, p: &Plane) {
        if !planes.contains(p) {
            planes.push(p.clone());
        }
    }
    let mut planes: Vec<Plane> = Vec::new();
    prog.facts.iter().for_each(|f| push(&mut planes, &f.plane));
    prog.rules.iter().for_each(|r| push(&mut planes, &r.plane));
    prog.planes.values().for_each(|p| push(&mut planes, p));
    let base = planes.clone();
    for (i, a) in base.iter().enumerate() {
        for b in &base[i + 1..] {
            if let Some(m) = prog.axes.plane_meet(a, b) {
                push(&mut planes, &m);
            }
        }
    }
    planes.sort_by_key(plane_to_string);
    planes
}

/// A distinct conflict: atom, kind and both source sets.
type ConflictId = (String, String, Vec<String>, Vec<String>);

fn scan_conflicts(prog: &Program) -> (Vec<FoundConflict>, BTreeSet<String>) {
    // One entry per distinct conflict (atom, kind, both source sets); for each,
    // the canonically smallest context in which it shows. Independent of the
    // order of statements and of contexts.
    let mut found: BTreeMap<ConflictId, (String, FoundConflict)> = BTreeMap::new();
    let mut errors = BTreeSet::new();
    for ctx in contexts(prog) {
        let out = eval::evaluate(prog, &ctx);
        errors.extend(out.errors.iter().cloned());
        for (key, c) in out.conflicts {
            let id = (
                key,
                format!("{:?}", c.kind),
                c.sources_pos.clone(),
                c.sources_neg.clone(),
            );
            let name = plane_to_string(&ctx);
            let keep = found.get(&id).is_none_or(|(old, _)| name < *old);
            if keep {
                found.insert(
                    id,
                    (
                        name,
                        FoundConflict {
                            context: ctx.clone(),
                            conflict: c,
                        },
                    ),
                );
            }
        }
    }
    (found.into_values().map(|(_, f)| f).collect(), errors)
}

fn answer(prog: &Program, q: &Query, errors: &mut BTreeSet<String>) -> QueryResult {
    let out = eval::evaluate(prog, &q.plane);
    errors.extend(out.errors.iter().cloned());
    let key = q.atom.key();
    let ckey = q.atom.complement().key();
    let pos_key = if q.atom.neg { &ckey } else { &key };
    let (verdict, explanation) = if let Some(c) = out.conflicts.get(pos_key) {
        let kind = if c.kind == ConflictKind::Hard {
            "hard contradiction"
        } else {
            "unresolved conflict"
        };
        (
            Verdict::Conflict,
            format!(
                "{kind}: for {} / against {}\n",
                c.sources_pos.join(", "),
                c.sources_neg.join(", ")
            ),
        )
    } else if out.db.contains_key(&key) {
        (Verdict::Yes, eval::explain(&out, &key))
    } else if out.db.contains_key(&ckey) {
        (Verdict::No, eval::explain(&out, &ckey))
    } else if let Some(g) = gap_for(prog, q, &out) {
        (Verdict::Gap, g)
    } else {
        let why = out
            .defeated
            .get(&key)
            .cloned()
            .unwrap_or_else(|| "nothing derives it or its negation".into());
        (Verdict::Unknown, format!("{why}\n"))
    };
    QueryResult {
        query: q.clone(),
        verdict,
        explanation,
    }
}

fn gap_for(prog: &Program, q: &Query, _out: &Outcome) -> Option<String> {
    let g = prog.gaps.get(&q.atom.rel)?;
    match &g.resolved_by {
        Some(axis) if q.plane.contains_key(axis) => None,
        Some(axis) => Some(format!(
            "gap `{}` ({}): resolved by choosing a value on axis `{axis}`\n",
            q.atom.rel, g.kind
        )),
        None => Some(format!("gap `{}` ({})\n", q.atom.rel, g.kind)),
    }
}

/// Canonical text of a report: conflicts and queries in a fixed order, with
/// explanations. Two runs of the same program must render identically, and so
/// must any reordering of its statements.
pub fn render(report: &Report) -> String {
    let mut lines: Vec<String> = report
        .diags
        .iter()
        .map(|d| format!("diag {:?} [{}] {}", d.level, d.code, d.msg))
        .chain(report.errors.iter().map(|e| format!("error {e}")))
        .collect();
    lines.sort();
    let mut conflicts: Vec<String> = report
        .conflicts
        .iter()
        .map(|c| {
            format!(
                "conflict {:?} {} for [{}] against [{}]",
                c.conflict.kind,
                c.conflict.positive,
                c.conflict.sources_pos.join(", "),
                c.conflict.sources_neg.join(", ")
            )
        })
        .collect();
    conflicts.sort();
    let mut queries: Vec<String> = report
        .queries
        .iter()
        .map(|q| {
            format!(
                "query {} @ {} -> {}\n{}",
                q.query.atom,
                plane_to_string(&q.query.plane),
                q.verdict,
                q.explanation
            )
        })
        .collect();
    queries.sort();
    queries.dedup();
    lines.extend(conflicts);
    lines.extend(queries);
    lines.join("\n")
}

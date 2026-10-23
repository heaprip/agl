//! Whole-program check: lint, contradiction scan over plane intersections,
//! and queries with their expected verdicts.

use std::collections::{BTreeMap, BTreeSet};

use crate::eval::{self, ConflictKind};
use crate::lint::{self, Diag, Level};
use crate::model::*;

#[derive(Debug)]
pub struct QueryResult {
    pub query: Query,
    /// The plane the query was answered in: its own, narrowed by `situate`.
    pub plane: Plane,
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

/// Outcomes already evaluated, by plane. Evaluation is a pure function of the
/// program and the plane, so the scan and every query in one plane share one.
struct Evals<'a> {
    prog: &'a Program,
    done: BTreeMap<Plane, eval::Outcome>,
}

impl Evals<'_> {
    fn get(&mut self, plane: &Plane) -> &eval::Outcome {
        if !self.done.contains_key(plane) {
            let out = eval::evaluate(self.prog, plane);
            self.done.insert(plane.clone(), out);
        }
        &self.done[plane]
    }
}

pub fn run(prog: &Program) -> Report {
    let diags = lint::lint(prog);
    let mut evals = Evals {
        prog,
        done: BTreeMap::new(),
    };
    let (conflicts, mut errors) = scan_conflicts(prog, &mut evals);
    let queries: Vec<QueryResult> = prog
        .queries
        .iter()
        .map(|q| answer(prog, q, &mut evals, &mut errors))
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

fn scan_conflicts(prog: &Program, evals: &mut Evals) -> (Vec<FoundConflict>, BTreeSet<String>) {
    // One entry per distinct conflict (atom, kind, both source sets); for each,
    // the canonically smallest context in which it shows. Independent of the
    // order of statements and of contexts.
    let mut found: BTreeMap<ConflictId, (String, FoundConflict)> = BTreeMap::new();
    let mut errors = BTreeSet::new();
    for ctx in contexts(prog) {
        let out = evals.get(&ctx);
        errors.extend(out.errors.iter().cloned());
        for (key, c) in out.conflicts.clone() {
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

/// Where a context belongs, found by the program itself.
pub struct Situation {
    pub plane: Plane,
    /// Grounds of every `situated` fact that narrowed the plane.
    pub grounds: String,
}

/// Narrows `base` by the `situated(context, axis, value)` atoms derived for
/// `context`, again and again until the plane stops changing. Narrowing only
/// makes more rules visible, and each axis can be fixed once, so this ends.
/// A context situated in two disjoint values of one axis is an error.
pub fn situate(prog: &Program, base: &Plane, context: &str) -> Result<Situation, String> {
    let mut plane = base.clone();
    let rounds = prog.axes_count() + 2;
    for _ in 0..rounds {
        let out = eval::evaluate(prog, &plane);
        let mut next = plane.clone();
        let mut grounds = String::new();
        for (key, (atom, _)) in &out.db {
            if atom.rel != "situated" || atom.neg {
                continue;
            }
            let get = |role: &str| {
                atom.args
                    .iter()
                    .find(|(r, _)| r == role)
                    .map(|(_, t)| t.to_string())
            };
            if get("context").as_deref() != Some(context) {
                continue;
            }
            let (Some(axis), Some(value)) = (get("axis"), get("value")) else {
                return Err(format!("`{key}` needs roles axis and value"));
            };
            if !prog.axes.has_value(&axis, &value) {
                return Err(format!("`{key}` names undeclared `{axis}:{value}`"));
            }
            let part = Plane::from([(axis.clone(), value.clone())]);
            next = prog.axes.plane_meet(&next, &part).ok_or_else(|| {
                format!(
                    "`{context}` is situated in disjoint planes: {} and {axis}:{value}",
                    plane_to_string(&next)
                )
            })?;
            grounds.push_str(&eval::explain(&out, key));
        }
        if next == plane {
            return Ok(Situation { plane, grounds });
        }
        plane = next;
    }
    Err(format!("situating `{context}` did not settle"))
}

/// The plane a query is answered in.
pub fn effective_plane(prog: &Program, q: &Query) -> Plane {
    match &q.situate {
        Some(ctx) => situate(prog, &q.plane, ctx).map_or_else(|_| q.plane.clone(), |s| s.plane),
        None => q.plane.clone(),
    }
}

fn answer(
    prog: &Program,
    q: &Query,
    evals: &mut Evals,
    errors: &mut BTreeSet<String>,
) -> QueryResult {
    let (plane, prelude) = match &q.situate {
        None => (q.plane.clone(), String::new()),
        Some(ctx) => match situate(prog, &q.plane, ctx) {
            Ok(s) => {
                let head = format!("`{ctx}` is situated in {}:\n", plane_to_string(&s.plane));
                let grounds: String = s.grounds.lines().map(|l| format!("  {l}\n")).collect();
                (s.plane, format!("{head}{grounds}so, in that plane:\n"))
            }
            Err(e) => {
                return QueryResult {
                    query: q.clone(),
                    plane: q.plane.clone(),
                    verdict: Verdict::Conflict,
                    explanation: format!("{e}\n"),
                };
            }
        },
    };
    let out = evals.get(&plane);
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
        (Verdict::Yes, eval::explain(out, &key))
    } else if out.db.contains_key(&ckey) {
        (Verdict::No, eval::explain(out, &ckey))
    } else if let Some(g) = gap_for(prog, q, &plane) {
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
        plane,
        verdict,
        explanation: format!("{prelude}{explanation}"),
    }
}

fn gap_for(prog: &Program, q: &Query, plane: &Plane) -> Option<String> {
    let g = prog.gaps.get(&q.atom.rel)?;
    match &g.resolved_by {
        Some(axis) if plane.contains_key(axis) => None,
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
                "conflict {:?} {} for [{}] against [{}] blame [{}]",
                c.conflict.kind,
                c.conflict.positive,
                c.conflict.sources_pos.join(", "),
                c.conflict.sources_neg.join(", "),
                c.conflict.blame.join(", ")
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
                plane_to_string(&q.plane),
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

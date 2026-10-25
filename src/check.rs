//! Whole-program check: lint, contradiction scan over plane intersections,
//! and queries with their expected verdicts.

use std::collections::{BTreeMap, BTreeSet};

use crate::concept;
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
pub struct CompareResult {
    pub compare: Compare,
    pub verdict: Result<Relation, String>,
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
    pub compares: Vec<CompareResult>,
}

impl Report {
    pub fn failed_queries(&self) -> impl Iterator<Item = &QueryResult> {
        self.queries
            .iter()
            .filter(|q| q.query.expect.is_some_and(|e| e != q.verdict))
    }

    pub fn failed_compares(&self) -> impl Iterator<Item = &CompareResult> {
        self.compares
            .iter()
            .filter(|c| c.compare.expect.is_some_and(|e| c.verdict != Ok(e)))
    }

    pub fn has_errors(&self) -> bool {
        self.diags.iter().any(|d| d.level == Level::Error)
            || !self.errors.is_empty()
            || self.compares.iter().any(|c| c.verdict.is_err())
    }
}

/// Outcomes already evaluated, by plane. Evaluation is a pure function of the
/// program and the plane, so the scan and every query in one plane share one.
pub(crate) struct Evals<'a> {
    pub(crate) prog: &'a Program,
    pub(crate) done: BTreeMap<Plane, eval::Outcome>,
    vis: Option<eval::Visibility>,
}

impl<'a> Evals<'a> {
    pub(crate) fn new(prog: &'a Program) -> Self {
        Evals {
            prog,
            done: BTreeMap::new(),
            vis: None,
        }
    }

    pub(crate) fn get(&mut self, plane: &Plane) -> &eval::Outcome {
        if !self.done.contains_key(plane) {
            let vis = self
                .vis
                .get_or_insert_with(|| eval::Visibility::new(self.prog));
            let out = eval::evaluate_in(self.prog, vis, plane);
            self.done.insert(plane.clone(), out);
        }
        &self.done[plane]
    }
}

pub fn run(prog: &Program) -> Report {
    let diags = lint::lint(prog);
    let mut evals = Evals::new(prog);
    let (conflicts, mut errors) = scan_conflicts(prog, &mut evals);
    let queries: Vec<QueryResult> = prog
        .queries
        .iter()
        .map(|q| answer(prog, q, &mut evals, &mut errors))
        .collect();
    let compares = prog
        .compares
        .iter()
        .map(|c| match concept::compare(prog, c) {
            Ok(r) => CompareResult {
                compare: c.clone(),
                verdict: Ok(r.relation),
                explanation: r.explanation,
            },
            Err(e) => CompareResult {
                compare: c.clone(),
                verdict: Err(e.clone()),
                explanation: format!("{e}\n"),
            },
        })
        .collect();
    Report {
        diags,
        errors: errors.into_iter().collect(),
        conflicts,
        queries,
        compares,
    }
}

/// Most contexts the contradiction scan visits; past it, a warning.
const MAX_CONTEXTS: usize = 4096;

/// Contexts worth checking: every plane in use, and every non-empty meet of
/// any number of them, closed to a fixpoint (meets of three planes and more
/// included). Returns false if the closure hit `MAX_CONTEXTS`.
pub(crate) fn contexts(prog: &Program) -> (Vec<Plane>, bool) {
    let mut planes: BTreeSet<Plane> = BTreeSet::new();
    prog.facts.iter().for_each(|f| {
        planes.insert(f.plane.clone());
    });
    prog.rules.iter().for_each(|r| {
        planes.insert(r.plane.clone());
    });
    prog.planes.values().for_each(|p| {
        planes.insert(p.clone());
    });
    let base: Vec<Plane> = planes.iter().cloned().collect();
    let mut frontier: Vec<Plane> = base.clone();
    let mut complete = true;
    while !frontier.is_empty() {
        let mut next = Vec::new();
        for a in &frontier {
            for b in &base {
                if let Some(m) = prog.axes.plane_meet(a, b)
                    && !planes.contains(&m)
                {
                    if planes.len() >= MAX_CONTEXTS {
                        complete = false;
                        continue;
                    }
                    planes.insert(m.clone());
                    next.push(m);
                }
            }
        }
        frontier = next;
    }
    let mut planes: Vec<Plane> = planes.into_iter().collect();
    planes.sort_by_key(plane_to_string);
    (planes, complete)
}

/// A distinct conflict: atom, kind and both source sets.
type ConflictId = (String, String, Vec<String>, Vec<String>);

fn scan_conflicts(prog: &Program, evals: &mut Evals) -> (Vec<FoundConflict>, BTreeSet<String>) {
    // One entry per distinct conflict (atom, kind, both source sets), shown in
    // the widest context where it shows: among contexts no other one of them
    // contains, the canonically smallest. Independent of the order of
    // statements and of contexts.
    let mut found: BTreeMap<ConflictId, Vec<(Plane, eval::Conflict)>> = BTreeMap::new();
    let mut errors = BTreeSet::new();
    let (contexts, complete) = contexts(prog);
    if !complete {
        errors.insert(format!(
            "contradiction scan stopped at {MAX_CONTEXTS} plane intersections: \
             conflicts in the rest are not reported"
        ));
    }
    for ctx in contexts {
        let out = evals.get(&ctx);
        errors.extend(out.errors.iter().cloned());
        for (key, c) in out.conflicts.clone() {
            let id = (
                key,
                format!("{:?}", c.kind),
                c.sources_pos.clone(),
                c.sources_neg.clone(),
            );
            found.entry(id).or_default().push((ctx.clone(), c));
        }
    }
    let widest = |seen: Vec<(Plane, eval::Conflict)>| {
        let wide: Vec<&(Plane, eval::Conflict)> = seen
            .iter()
            .filter(|(p, _)| !seen.iter().any(|(q, _)| prog.axes.strictly_within(p, q)))
            .collect();
        let (context, conflict) = wide
            .into_iter()
            .min_by_key(|(p, _)| plane_to_string(p))
            .expect("a conflict shows in some context")
            .clone();
        FoundConflict { context, conflict }
    };
    (found.into_values().map(widest).collect(), errors)
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
/// A context situated in two disjoint values of one axis is an error. So is a
/// plane that undermines itself: rules visible only after narrowing may defeat
/// a `situated` atom the narrowing rested on, and then the plane has no
/// grounds.
pub fn situate(prog: &Program, base: &Plane, context: &str) -> Result<Situation, String> {
    let mut evals = Evals::new(prog);
    situate_in(&mut evals, base, context)
}

/// `situate` sharing the outcomes already evaluated for the report.
fn situate_in(evals: &mut Evals, base: &Plane, context: &str) -> Result<Situation, String> {
    let prog = evals.prog;
    let mut plane = base.clone();
    let mut used: BTreeSet<String> = BTreeSet::new();
    let rounds = prog.axes_count() + 2;
    for _ in 0..rounds {
        let out = evals.get(&plane);
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
            grounds.push_str(&eval::explain(out, key));
            used.insert(key.clone());
        }
        if next == plane {
            let lost: Vec<&String> = used.iter().filter(|k| !out.db.contains_key(*k)).collect();
            if let Some(k) = lost.first() {
                let why = out
                    .defeated
                    .get(*k)
                    .cloned()
                    .unwrap_or_else(|| "it is not derived there".into());
                return Err(format!(
                    "`{context}` undermines its own plane: it was situated by `{k}`, \
                     which does not hold in {}: {why}",
                    plane_to_string(&plane)
                ));
            }
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
        Some(ctx) => match situate_in(evals, &q.plane, ctx) {
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
    let g = prog.gaps.get(q.atom.rel.as_str())?;
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
    let mut compares: Vec<String> = report
        .compares
        .iter()
        .map(|c| {
            let verdict = match &c.verdict {
                Ok(r) => r.to_string(),
                Err(_) => "error".into(),
            };
            format!(
                "compare {} @ {} vs {} @ {} -> {verdict}\n{}",
                c.compare.left.0,
                plane_to_string(&c.compare.left.1),
                c.compare.right.0,
                plane_to_string(&c.compare.right.1),
                c.explanation
            )
        })
        .collect();
    compares.sort();
    compares.dedup();
    lines.extend(conflicts);
    lines.extend(queries);
    lines.extend(compares);
    lines.join("\n")
}

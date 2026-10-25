//! Static checks of a program, before any evaluation.

use std::collections::BTreeSet;

use crate::model::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub line: usize,
    pub level: Level,
    pub code: &'static str,
    pub msg: String,
}

pub fn lint(prog: &Program) -> Vec<Diag> {
    let mut out = Vec::new();
    let normative_plane = |p: &Plane| p.keys().any(|a| prog.normative_axes.contains(a));

    for f in &prog.facts {
        check_roles(prog, &f.atom, f.line, &mut out);
        if !f.atom.is_ground() {
            out.push(err(
                f.line,
                "unground-fact",
                format!("fact `{}` has variables", f.id),
            ));
        }
        if prog.normative_preds.contains(f.atom.rel.as_str()) && !normative_plane(&f.plane) {
            out.push(err(
                f.line,
                "is-ought",
                format!(
                    "fact `{}` states a norm `{}` in a plane without a normative axis",
                    f.id, f.atom.rel
                ),
            ));
        }
    }

    let rule_ids: BTreeSet<&str> = prog.rules.iter().map(|r| r.id.as_str()).collect();
    for r in &prog.rules {
        check_roles(prog, &r.head, r.line, &mut out);
        let mut bound: BTreeSet<&str> = BTreeSet::new();
        for lit in &r.body {
            match lit {
                Lit::Atom(a) => {
                    check_roles(prog, a, r.line, &mut out);
                    bound.extend(a.vars());
                }
                Lit::Cmp(Expr::Term(Term::Var(v)), CmpOp::Eq, _) => {
                    bound.insert(v.as_str());
                }
                Lit::Agg { var, over, .. } => {
                    // Variables inside `over` are local to the aggregate.
                    over.iter()
                        .for_each(|a| check_roles(prog, a, r.line, &mut out));
                    bound.insert(var.as_str());
                }
                Lit::Cmp(..) => {}
            }
        }
        let unbound: Vec<&str> = r.head.vars().filter(|v| !bound.contains(v)).collect();
        if !unbound.is_empty() {
            out.push(err(
                r.line,
                "unsafe-rule",
                format!(
                    "rule `{}`: head variables {unbound:?} are not bound by the body",
                    r.id
                ),
            ));
        }
        if prog.normative_preds.contains(r.head.rel.as_str()) && !normative_plane(&r.plane) {
            out.push(err(
                r.line,
                "is-ought",
                format!(
                    "rule `{}` concludes a norm `{}` in a plane without a normative axis: a normative conclusion needs a normative premise",
                    r.id, r.head.rel
                ),
            ));
        }
    }

    let (_, cyclic) = crate::eval::strata(&prog.rules);
    if !cyclic.is_empty() {
        out.push(err(
            0,
            "aggregate-cycle",
            format!("relations {cyclic:?} depend on their own aggregate and cannot be stratified"),
        ));
    }

    for u in &prog.uniques {
        if let Some(roles) = prog.relations.get(u.rel.as_str()) {
            for role in std::iter::once(&u.role).chain(&u.by) {
                if !roles.contains(role) {
                    out.push(err(
                        u.line,
                        "unknown-role",
                        format!("`unique {}` names unknown role `{role}`", u.rel),
                    ));
                }
            }
        }
    }

    for (w, l) in &prog.defeats {
        for id in [w, l] {
            if !rule_ids.contains(id.as_str()) {
                out.push(err(
                    0,
                    "unknown-rule",
                    format!("`defeats` names unknown rule `{id}`"),
                ));
            }
        }
    }
    if prog.clean.is_some() {
        ready_made(prog, &mut out);
    }
    out
}

/// In a clean world (`world clean`, H72) the kernel rejects whatever comes
/// ready-made instead of being found: numbers and units, arithmetic, order
/// of numbers, aggregates, hand-given definitions and names, given nesting
/// and functionality, included libraries. One error per statement.
fn ready_made(prog: &Program, out: &mut Vec<Diag>) {
    let mut found: Vec<(usize, Vec<&'static str>)> = Vec::new();
    let atom = |a: &Atom, kinds: &mut Vec<&'static str>| {
        if a.args.iter().any(|(_, t)| matches!(t, Term::Num(..))) {
            kinds.push("number");
        }
    };
    for f in &prog.facts {
        let mut k = Vec::new();
        atom(&f.atom, &mut k);
        found.push((f.line, k));
    }
    for r in &prog.rules {
        let mut k = Vec::new();
        atom(&r.head, &mut k);
        for lit in &r.body {
            match lit {
                Lit::Atom(a) => atom(a, &mut k),
                Lit::Cmp(l, op, r) => {
                    if !matches!(op, CmpOp::Eq | CmpOp::Ne) {
                        k.push("order of numbers");
                    }
                    for e in [l, r] {
                        expr_kinds(e, &mut k);
                    }
                }
                Lit::Agg { .. } => k.push("aggregate"),
            }
        }
        found.push((r.line, k));
    }
    for q in &prog.queries {
        let mut k = Vec::new();
        atom(&q.atom, &mut k);
        found.push((q.line, k));
    }
    for b in &prog.forbids {
        let mut k = Vec::new();
        atom(&b.atom, &mut k);
        found.push((b.line, k));
    }
    let hand = [
        prog.concepts
            .iter()
            .map(|c| (c.line, "concept"))
            .collect::<Vec<_>>(),
        prog.words.iter().map(|w| (w.line, "word")).collect(),
        prog.compares.iter().map(|c| (c.line, "compare")).collect(),
        prog.nestings.iter().map(|n| (n.line, "nesting")).collect(),
        prog.uniques.iter().map(|u| (u.line, "unique")).collect(),
    ];
    for (line, kind) in hand.into_iter().flatten() {
        found.push((line, vec![kind]));
    }
    for (line, stmt) in &prog.given {
        let kind = match stmt.split_whitespace().next() {
            Some("include") => "include",
            Some("quantity") => "quantity",
            Some("unit") => "unit",
            _ => "cover",
        };
        found.push((*line, vec![kind]));
    }
    // Rules compiled from a concept share its line: report the line once.
    found.sort();
    let mut lines: Vec<(usize, Vec<&'static str>)> = Vec::new();
    for (line, mut kinds) in found {
        match lines.last_mut() {
            Some((l, k)) if *l == line => k.append(&mut kinds),
            _ => lines.push((line, kinds)),
        }
    }
    for (line, mut kinds) in lines {
        kinds.sort();
        kinds.dedup();
        if !kinds.is_empty() {
            out.push(err(
                line,
                "ready-made",
                format!("clean world: given ready-made ({})", kinds.join(", ")),
            ));
        }
    }
}

fn expr_kinds(e: &Expr, kinds: &mut Vec<&'static str>) {
    match e {
        Expr::Term(Term::Num(..)) => kinds.push("number"),
        Expr::Term(_) => {}
        Expr::Bin(l, _, r) => {
            kinds.push("arithmetic");
            expr_kinds(l, kinds);
            expr_kinds(r, kinds);
        }
    }
}

fn check_roles(prog: &Program, a: &Atom, line: usize, out: &mut Vec<Diag>) {
    let Some(roles) = prog.relations.get(a.rel.as_str()) else {
        return;
    };
    for (role, _) in &a.args {
        if !roles.iter().any(|r| role == r) {
            out.push(err(
                line,
                "unknown-role",
                format!(
                    "`{}` has no role `{role}` (declared: {})",
                    a.rel,
                    roles.join(", ")
                ),
            ));
        }
    }
}

fn err(line: usize, code: &'static str, msg: String) -> Diag {
    Diag {
        line,
        level: Level::Error,
        code,
        msg,
    }
}

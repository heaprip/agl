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
        if prog.normative_preds.contains(&f.atom.rel) && !normative_plane(&f.plane) {
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
        if prog.normative_preds.contains(&r.head.rel) && !normative_plane(&r.plane) {
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
    out
}

fn check_roles(prog: &Program, a: &Atom, line: usize, out: &mut Vec<Diag>) {
    let Some(roles) = prog.relations.get(&a.rel) else {
        return;
    };
    for (role, _) in &a.args {
        if !roles.contains(role) {
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

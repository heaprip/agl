//! Data model of a program: terms, atoms, literals, facts, rules, queries.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::plane::Axes;

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Sym(String),
    Num(f64),
    Var(String),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Sym(s) => write!(f, "{s}"),
            Term::Var(v) => write!(f, "?{v}"),
            Term::Num(n) if n.fract() == 0.0 && n.abs() < 1e15 => write!(f, "{}", *n as i64),
            Term::Num(n) => write!(f, "{n}"),
        }
    }
}

/// A relation instance with named roles. Roles are kept sorted, so two atoms
/// with the same content print the same and share a key.
#[derive(Clone, Debug, PartialEq)]
pub struct Atom {
    pub rel: String,
    pub args: Vec<(String, Term)>,
    pub neg: bool,
}

impl Atom {
    pub fn new(rel: String, mut args: Vec<(String, Term)>, neg: bool) -> Self {
        args.sort_by(|a, b| a.0.cmp(&b.0));
        Atom { rel, args, neg }
    }

    pub fn key(&self) -> String {
        self.to_string()
    }

    pub fn complement(&self) -> Atom {
        Atom {
            neg: !self.neg,
            ..self.clone()
        }
    }

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|(_, t)| !matches!(t, Term::Var(_)))
    }

    pub fn vars(&self) -> impl Iterator<Item = &str> {
        self.args.iter().filter_map(|(_, t)| match t {
            Term::Var(v) => Some(v.as_str()),
            _ => None,
        })
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.neg {
            write!(f, "¬")?;
        }
        write!(f, "{}(", self.rel)?;
        for (i, (role, term)) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{role}: {term}")?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Term(Term),
    Bin(Box<Expr>, char, Box<Expr>),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CmpOp {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

#[derive(Clone, Debug)]
pub enum Lit {
    Atom(Atom),
    Cmp(Expr, CmpOp, Expr),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strength {
    Strict,
    Defeasible,
}

/// Axis constraints: axis name to value.
pub type Plane = BTreeMap<String, String>;

pub fn plane_to_string(p: &Plane) -> String {
    if p.is_empty() {
        return "{}".into();
    }
    let parts: Vec<String> = p.iter().map(|(a, v)| format!("{a}:{v}")).collect();
    format!("{{{}}}", parts.join(", "))
}

#[derive(Clone, Debug)]
pub struct Fact {
    pub id: String,
    pub atom: Atom,
    pub plane: Plane,
    pub status: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub id: String,
    pub head: Atom,
    pub body: Vec<Lit>,
    pub strength: Strength,
    pub plane: Plane,
    pub line: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Yes,
    No,
    Unknown,
    Conflict,
    Gap,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Verdict::Yes => "yes",
            Verdict::No => "no",
            Verdict::Unknown => "unknown",
            Verdict::Conflict => "conflict",
            Verdict::Gap => "gap",
        };
        write!(f, "{s}")
    }
}

#[derive(Clone, Debug)]
pub struct Query {
    pub atom: Atom,
    pub plane: Plane,
    pub expect: Option<Verdict>,
    pub line: usize,
}

/// A declared typed gap: the term cannot be answered from the trunk; `resolved_by`
/// names the axis whose choice resolves it (for evaluative-by-design gaps).
#[derive(Clone, Debug)]
pub struct Gap {
    pub kind: String,
    pub resolved_by: Option<String>,
}

#[derive(Default, Debug)]
pub struct Program {
    pub axes: Axes,
    pub planes: BTreeMap<String, Plane>,
    pub facts: Vec<Fact>,
    pub rules: Vec<Rule>,
    pub defeats: BTreeSet<(String, String)>,
    pub normative_preds: BTreeSet<String>,
    pub normative_axes: BTreeSet<String>,
    pub relations: BTreeMap<String, Vec<String>>,
    pub gaps: BTreeMap<String, Gap>,
    pub queries: Vec<Query>,
}

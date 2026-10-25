//! Data model of a program: terms, atoms, literals, facts, rules, queries.

use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;

use crate::plane::Axes;
use crate::units::Dim;

/// A name (relation, role, symbol, source) shared by every atom that uses
/// it: the text is stored once, atoms hold references (H61, step 3a). It
/// compares and prints as its text, so order and output stay those of text.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Name(Rc<str>);

impl Name {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Deref for Name {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Name {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl From<&str> for Name {
    fn from(s: &str) -> Self {
        Name(Rc::from(s))
    }
}

impl From<String> for Name {
    fn from(s: String) -> Self {
        Name(Rc::from(s))
    }
}

impl From<&String> for Name {
    fn from(s: &String) -> Self {
        Name(Rc::from(s.as_str()))
    }
}

impl PartialEq<str> for Name {
    fn eq(&self, o: &str) -> bool {
        *self.0 == *o
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, o: &&str) -> bool {
        *self.0 == **o
    }
}

impl PartialEq<String> for Name {
    fn eq(&self, o: &String) -> bool {
        *self.0 == **o
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

/// Hands out one `Name` per text, so equal names share their storage.
#[derive(Default)]
pub struct Names(BTreeSet<Name>);

impl Names {
    pub fn get(&mut self, s: &str) -> Name {
        if let Some(n) = self.0.get(s) {
            return n.clone();
        }
        let n = Name::from(s);
        self.0.insert(n.clone());
        n
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Sym(Name),
    /// A value in SI with its dimension.
    Num(f64, Dim),
    Var(String),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Sym(s) => write!(f, "{s}"),
            Term::Var(v) => write!(f, "?{v}"),
            Term::Num(n, dim) => {
                if n.fract() == 0.0 && n.abs() < 1e15 {
                    write!(f, "{}", *n as i64)?;
                } else {
                    write!(f, "{n}")?;
                }
                if !dim.is_none() {
                    write!(f, "[{dim}]")?;
                }
                Ok(())
            }
        }
    }
}

/// A relation instance with named roles. Roles are kept sorted, so two atoms
/// with the same content print the same and share a key.
#[derive(Clone, Debug, PartialEq)]
pub struct Atom {
    pub rel: Name,
    pub args: Vec<(Name, Term)>,
    pub neg: bool,
}

impl Atom {
    pub fn new(rel: Name, mut args: Vec<(Name, Term)>, neg: bool) -> Self {
        args.sort_by(|a, b| a.0.cmp(&b.0));
        args.shrink_to_fit();
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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum AggFn {
    Sum,
    Count,
    Min,
    Max,
}

#[derive(Clone, Debug)]
pub enum Lit {
    Atom(Atom),
    Cmp(Expr, CmpOp, Expr),
    /// `?var = func(expr) over (atoms)`: aggregates over the distinct solutions
    /// of `over` under the current binding. Requires `over` to be complete,
    /// so its relations sit in a lower stratum than the rule head.
    Agg {
        var: String,
        func: AggFn,
        expr: Expr,
        over: Vec<Atom>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strength {
    Strict,
    Defeasible,
}

/// Axis constraints: axis name to value.
pub type Plane = BTreeMap<String, String>;

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Term(t) => write!(f, "{t}"),
            Expr::Bin(l, op, r) => write!(f, "({l} {op} {r})"),
        }
    }
}

impl fmt::Display for CmpOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
            CmpOp::Eq => "=",
            CmpOp::Ne => "!=",
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Atom(a) => write!(f, "{a}"),
            Lit::Cmp(l, op, r) => write!(f, "{l} {op} {r}"),
            Lit::Agg {
                var,
                func,
                expr,
                over,
            } => {
                let name = match func {
                    AggFn::Sum => "sum",
                    AggFn::Count => "count",
                    AggFn::Min => "min",
                    AggFn::Max => "max",
                };
                let over: Vec<String> = over.iter().map(Atom::to_string).collect();
                write!(f, "?{var} = {name}({expr}) over ({})", over.join(", "))
            }
        }
    }
}

/// A plane as it is written after `@`: `axis:value + axis:value`.
pub fn plane_to_spec(p: &Plane) -> String {
    let parts: Vec<String> = p.iter().map(|(a, v)| format!("{a}:{v}")).collect();
    parts.join(" + ")
}

impl Program {
    pub fn axes_count(&self) -> usize {
        self.axes.count()
    }
}

impl Rule {
    /// The rule in the case notation, parseable back.
    pub fn to_source(&self) -> String {
        let strength = match self.strength {
            Strength::Strict => "strict",
            Strength::Defeasible => "defeasible",
        };
        let body: Vec<String> = self.body.iter().map(Lit::to_string).collect();
        format!(
            "rule {} {strength} @ {}: {} <- {}",
            self.id,
            plane_to_spec(&self.plane),
            self.head,
            body.join(", ")
        )
    }
}

pub fn plane_to_string(p: &Plane) -> String {
    if p.is_empty() {
        return "{}".into();
    }
    let parts: Vec<String> = p.iter().map(|(a, v)| format!("{a}:{v}")).collect();
    format!("{{{}}}", parts.join(", "))
}

#[derive(Clone, Debug)]
pub struct Fact {
    pub id: Name,
    pub atom: Atom,
    pub plane: Plane,
    pub status: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Rule {
    pub id: Name,
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
    /// `situate CONTEXT`: the plane is narrowed by the `situated` facts the
    /// program derives about this context, before the query is answered.
    pub situate: Option<String>,
    pub expect: Option<Verdict>,
    /// A held-out expectation: checked, but never used to fit a hypothesis.
    pub heldout: bool,
    pub line: usize,
}

/// A declared typed gap: the term cannot be answered from the trunk; `resolved_by`
/// names the axis whose choice resolves it (for evaluative-by-design gaps).
#[derive(Clone, Debug)]
pub struct Gap {
    pub kind: String,
    pub resolved_by: Option<String>,
}

/// `unique REL(role) by (keys)`: for fixed key values, at most one value of `role`.
#[derive(Clone, Debug)]
pub struct Unique {
    pub rel: String,
    pub role: String,
    pub by: Vec<String>,
    pub line: usize,
}

/// `forbid LITERAL @ SPEC`: an integrity constraint; deriving a match is a violation.
#[derive(Clone, Debug)]
pub struct Forbid {
    pub atom: Atom,
    pub plane: Plane,
    pub line: usize,
}

/// `concept NAME(role: ?v, ...) @ SPEC: BODY`: one sense of a concept. The
/// body is necessary and sufficient, so the kernel both recognizes the concept
/// (it is compiled into a strict rule) and compares concepts by their
/// definitions (`crate::concept`). Senses of one name are a union.
#[derive(Clone, Debug)]
pub struct Concept {
    pub head: Atom,
    /// Positive atoms and `?a != ?b`.
    pub body: Vec<Lit>,
    pub plane: Plane,
    pub line: usize,
}

/// `word LANG WORD = CONCEPT`: how a language names a concept.
#[derive(Clone, Debug)]
pub struct Word {
    pub lang: String,
    pub word: String,
    pub concept: String,
    pub line: usize,
}

/// How two concepts relate by definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation {
    Same,
    /// The left one is a special case of the right one.
    Below,
    Above,
    Apart,
    /// Against a relation defined by rules: only "below" can be shown.
    NotBelow,
    /// Against rules that are not monotone (aggregates, comparisons,
    /// defeasible rules, negation): no counterexample among the canonical
    /// worlds, but that does not prove "below".
    Unknown,
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Relation::Same => "same",
            Relation::Below => "below",
            Relation::Above => "above",
            Relation::Apart => "apart",
            Relation::NotBelow => "not_below",
            Relation::Unknown => "unknown",
        };
        write!(f, "{s}")
    }
}

/// `compare NAME @ SPEC vs NAME @ SPEC [expect RELATION]`.
#[derive(Clone, Debug)]
pub struct Compare {
    pub left: (String, Plane),
    pub right: (String, Plane),
    pub expect: Option<Relation>,
    pub line: usize,
}

/// `nesting ID: N(a, b) by E(x, y)`: N is the transitive closure of E.
/// Parsing adds the two strict rules `ID_base` and `ID_step` (see
/// `Nesting::rules`), which every module reads as ordinary rules; evaluation
/// derives their atoms from labels instead of iterating them (H61).
#[derive(Clone, Debug)]
pub struct Nesting {
    pub id: Name,
    pub rel: Name,
    /// (species role, genus role) of N
    pub roles: (Name, Name),
    pub edge: Name,
    /// (species role, genus role) of E
    pub edge_roles: (Name, Name),
    /// `... lazy`: atoms of N are made only when a rule body asks for them
    /// (H61, step 2b), if nothing else reads N; see `eval`.
    pub lazy: bool,
    pub line: usize,
}

impl Nesting {
    pub fn base_id(&self) -> Name {
        format!("{}_base", self.id).into()
    }

    pub fn step_id(&self) -> Name {
        format!("{}_step", self.id).into()
    }

    /// `ID_base: N(a: ?x, b: ?y) <- E(x: ?x, y: ?y)` and
    /// `ID_step: N(a: ?x, b: ?y) <- E(x: ?x, y: ?z), N(a: ?z, b: ?y)`.
    pub fn rules(&self) -> [Rule; 2] {
        let var = |v: &str| Term::Var(v.to_string());
        let n = |a: &str, b: &str| {
            Atom::new(
                self.rel.clone(),
                vec![
                    (self.roles.0.clone(), var(a)),
                    (self.roles.1.clone(), var(b)),
                ],
                false,
            )
        };
        let e = |a: &str, b: &str| {
            Atom::new(
                self.edge.clone(),
                vec![
                    (self.edge_roles.0.clone(), var(a)),
                    (self.edge_roles.1.clone(), var(b)),
                ],
                false,
            )
        };
        let rule = |id: Name, body: Vec<Lit>| Rule {
            id,
            head: n("x", "y"),
            body,
            strength: Strength::Strict,
            plane: Plane::new(),
            line: self.line,
        };
        [
            rule(self.base_id(), vec![Lit::Atom(e("x", "y"))]),
            rule(
                self.step_id(),
                vec![Lit::Atom(e("x", "z")), Lit::Atom(n("z", "y"))],
            ),
        ]
    }
}

#[derive(Clone, Default, Debug)]
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
    pub uniques: Vec<Unique>,
    /// Status -> rank, from `status A > B > C`; higher is more trusted.
    pub status_rank: BTreeMap<String, usize>,
    pub forbids: Vec<Forbid>,
    pub concepts: Vec<Concept>,
    pub words: Vec<Word>,
    pub compares: Vec<Compare>,
    /// `cover female(person) | male(person)`: every individual is in one of
    /// the alternatives. Used only when concepts are compared.
    pub covers: Vec<Vec<(String, String)>>,
    /// Declared quantities and units (decision 23).
    pub units: crate::units::Units,
    pub nestings: Vec<Nesting>,
    /// Line of `world clean`: the kernel itself rejects anything given
    /// ready-made (H72, `docs/impl/clean.md`).
    pub clean: Option<usize>,
    /// Statements that leave no other trace in the model, by line: `quantity`,
    /// `unit`, `cover`, `include` (the last from `parse_file`).
    pub given: Vec<(usize, String)>,
}

//! PoC of the agl v0 metakernel.
//!
//! A program is a set of facts and rules, each holding in a plane. A plane is
//! a set of axis constraints; axis values form a tree (nesting), siblings are
//! disjoint unless an overlap is declared. Contradictions are looked for only
//! where planes intersect. See `docs/decisions.md` (decision 17) for the
//! kernel this implements and `docs/impl/poc.md` for the semantics chosen.

pub mod check;
pub mod eval;
pub mod lint;
pub mod model;
pub mod parse;
pub mod plane;
pub mod propose;
pub mod reflect;
pub mod sim;
pub mod units;

pub use check::{Report, render, run};
pub use parse::{parse, parse_file};

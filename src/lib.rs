//! PoC of the agl v0 metakernel.
//!
//! A program is a set of facts and rules, each holding in a plane. A plane is
//! a set of axis constraints; axis values form a tree (nesting), siblings are
//! disjoint unless an overlap is declared. Contradictions are looked for only
//! where planes intersect. See `docs/decisions.md` (decision 17) for the
//! kernel this implements and `docs/impl/poc.md` for the semantics chosen.

pub mod atlas;
pub mod bank;
pub mod check;
pub mod concept;
pub mod develop;
pub mod eval;
pub mod exists;
pub mod extent;
pub mod free;
pub mod journal;
pub mod label;
pub mod layer;
pub mod learn;
pub mod lint;
pub mod model;
pub mod parse;
pub mod plane;
pub mod propose;
pub mod reflect;
pub mod rewrite;
pub mod sat;
pub mod scale;
pub mod sim;
pub mod units;

pub use check::{Report, render, run};
pub use parse::{parse, parse_file, read_expanded};

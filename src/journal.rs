//! The journal of what the kernel derived (`docs/impl/atlas.md` §9).
//!
//! One record per result: what it is, from which records and by which step
//! it came, how far it was checked (the stage: a theorem is the state of a
//! theory, not a timeless fact), and whether the kernel stands on it. A
//! record's id hashes all of that together with the version of the tools,
//! so a record made by other tools, or edited by hand, does not check.
//! Records are kept in the order made; a run from nothing must give the
//! same journal byte for byte.

use std::collections::BTreeMap;
use std::fmt::Write as _;

/// The version of the tools a record was made with: a change in how
/// anything is derived must change it.
pub const TOOLS: &str = "atlas-9";

/// The most a journal may hold, in bytes of its text: development stops
/// before it grows past this.
pub const MAX_BYTES: usize = 1 << 20;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub id: u64,
    pub kind: String,
    pub step: String,
    pub stage: String,
    pub anchored: bool,
    pub from: Vec<u64>,
    pub body: String,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct Journal {
    pub records: Vec<Record>,
    index: BTreeMap<u64, usize>,
    bytes: usize,
}

/// FNV-1a, 64 bits: stable across runs and machines. A check against
/// mistakes and stale tools, not against forgery.
fn hash(parts: &[&str]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for p in parts {
        for b in p.bytes().chain([0u8]) {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    }
    h
}

fn id_of(kind: &str, step: &str, stage: &str, anchored: bool, from: &[u64], body: &str) -> u64 {
    let from: Vec<String> = from.iter().map(|f| format!("{f:016x}")).collect();
    hash(&[
        TOOLS,
        kind,
        step,
        stage,
        if anchored { "anchored" } else { "" },
        &from.join(","),
        body,
    ])
}

impl Journal {
    pub fn new() -> Journal {
        Journal::default()
    }

    /// Adds a record, or finds the same one already there; its id.
    pub fn add(
        &mut self,
        kind: &str,
        step: &str,
        stage: &str,
        anchored: bool,
        from: &[u64],
        body: &str,
    ) -> u64 {
        assert!(
            !body.contains('\n') && ![kind, step, stage].iter().any(|s| s.contains([' ', '\n']))
        );
        let id = id_of(kind, step, stage, anchored, from, body);
        if !self.index.contains_key(&id) {
            self.bytes += 64 + kind.len() + step.len() + stage.len() + 17 * from.len() + body.len();
            self.index.insert(id, self.records.len());
            self.records.push(Record {
                id,
                kind: kind.into(),
                step: step.into(),
                stage: stage.into(),
                anchored,
                from: from.to_vec(),
                body: body.into(),
            });
        }
        id
    }

    /// Whether the journal has reached `MAX_BYTES`, roughly.
    pub fn full(&self) -> bool {
        self.bytes >= MAX_BYTES
    }

    pub fn get(&self, id: u64) -> Option<&Record> {
        self.index.get(&id).map(|&i| &self.records[i])
    }

    /// One line per record: id, kind, step, stage, anchor mark, sources,
    /// then the body after " | ".
    pub fn text(&self) -> String {
        let mut out = format!("# agl journal, tools {TOOLS}\n");
        for r in &self.records {
            let from: Vec<String> = r.from.iter().map(|f| format!("{f:016x}")).collect();
            let from = if from.is_empty() {
                "-".into()
            } else {
                from.join(",")
            };
            let mark = if r.anchored { "anchored" } else { "-" };
            writeln!(
                out,
                "{:016x} {} {} {} {} {} | {}",
                r.id, r.kind, r.step, r.stage, mark, from, r.body
            )
            .unwrap();
        }
        out
    }

    /// Reads a journal back. Every id must match its record under the
    /// current tools, and every source must come before the record using it.
    pub fn parse(text: &str) -> Result<Journal, String> {
        let mut j = Journal::new();
        for (no, line) in text.lines().enumerate() {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let at = |what: &str| format!("line {}: {what}", no + 1);
            let (head, body) = line.split_once(" | ").ok_or_else(|| at("no body"))?;
            let f: Vec<&str> = head.split(' ').collect();
            let [id, kind, step, stage, mark, from] = f[..] else {
                return Err(at("bad head"));
            };
            let id = u64::from_str_radix(id, 16).map_err(|_| at("bad id"))?;
            let from: Vec<u64> = if from == "-" {
                Vec::new()
            } else {
                from.split(',')
                    .map(|s| u64::from_str_radix(s, 16).map_err(|_| at("bad source")))
                    .collect::<Result<_, _>>()?
            };
            if let Some(missing) = from.iter().find(|f| j.get(**f).is_none()) {
                return Err(at(&format!("source {missing:016x} not before")));
            }
            let anchored = mark == "anchored";
            if id_of(kind, step, stage, anchored, &from, body) != id {
                return Err(at("id does not check (edited, or other tools)"));
            }
            j.add(kind, step, stage, anchored, &from, body);
        }
        Ok(j)
    }
}

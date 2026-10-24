//! Planes as axis constraints over value trees.
//!
//! On one axis, a value is within its ancestors. Siblings are disjoint unless
//! an overlap is declared between them or their ancestors; the meet of two
//! overlapping values is the composite `a∩b`, which is within both.

use std::collections::{BTreeMap, BTreeSet};

use crate::model::Plane;

const MEET: char = '∩';

#[derive(Default, Debug, Clone)]
pub struct Axes {
    /// axis -> value -> parent
    values: BTreeMap<String, BTreeMap<String, Option<String>>>,
    /// (axis, a, b) with a < b
    overlaps: BTreeSet<(String, String, String)>,
}

impl Axes {
    pub fn count(&self) -> usize {
        self.values.len()
    }

    pub fn declare_axis(&mut self, axis: &str) {
        self.values.entry(axis.to_string()).or_default();
    }

    pub fn has_axis(&self, axis: &str) -> bool {
        self.values.contains_key(axis)
    }

    pub fn declare_value(
        &mut self,
        axis: &str,
        value: &str,
        parent: Option<&str>,
    ) -> Result<(), String> {
        let vals = self
            .values
            .get_mut(axis)
            .ok_or_else(|| format!("unknown axis `{axis}`"))?;
        if let Some(p) = parent
            && !vals.contains_key(p)
        {
            return Err(format!("unknown parent `{p}` on axis `{axis}`"));
        }
        vals.insert(value.to_string(), parent.map(str::to_string));
        Ok(())
    }

    pub fn declare_overlap(&mut self, axis: &str, a: &str, b: &str) -> Result<(), String> {
        if !self.has_value(axis, a) || !self.has_value(axis, b) {
            return Err(format!("overlap on `{axis}` names an undeclared value"));
        }
        let (x, y) = if a < b { (a, b) } else { (b, a) };
        self.overlaps
            .insert((axis.to_string(), x.to_string(), y.to_string()));
        Ok(())
    }

    /// Direct children of `value` on `axis`, in canonical order.
    pub fn children(&self, axis: &str, value: &str) -> Vec<String> {
        self.values
            .get(axis)
            .map(|vals| {
                vals.iter()
                    .filter(|(_, p)| p.as_deref() == Some(value))
                    .map(|(v, _)| v.clone())
                    .collect()
            })
            .unwrap_or_default()
    }

    pub fn parent(&self, axis: &str, value: &str) -> Option<String> {
        self.values.get(axis)?.get(value)?.clone()
    }

    /// Moves `value` under `new_parent`, which must exist and not lie below it.
    pub fn reparent(&mut self, axis: &str, value: &str, new_parent: &str) -> Result<(), String> {
        if self.value_within(axis, new_parent, value) {
            return Err(format!("`{new_parent}` lies within `{value}`"));
        }
        let vals = self
            .values
            .get_mut(axis)
            .ok_or_else(|| format!("unknown axis `{axis}`"))?;
        if !vals.contains_key(new_parent) || !vals.contains_key(value) {
            return Err(format!("unknown value on axis `{axis}`"));
        }
        vals.insert(value.to_string(), Some(new_parent.to_string()));
        Ok(())
    }

    pub fn has_value(&self, axis: &str, value: &str) -> bool {
        let Some(vals) = self.values.get(axis) else {
            return false;
        };
        value.split(MEET).all(|v| vals.contains_key(v))
    }

    fn ancestors(&self, axis: &str, value: &str) -> Vec<String> {
        let mut out = vec![value.to_string()];
        let Some(vals) = self.values.get(axis) else {
            return out;
        };
        let mut cur = value;
        while let Some(Some(parent)) = vals.get(cur) {
            out.push(parent.clone());
            cur = parent;
        }
        out
    }

    /// `a` is within `b` on `axis`.
    pub fn value_within(&self, axis: &str, a: &str, b: &str) -> bool {
        if b.contains(MEET) {
            return b.split(MEET).all(|part| self.value_within(axis, a, part));
        }
        if a.contains(MEET) {
            return a.split(MEET).any(|part| self.value_within(axis, part, b));
        }
        // Up the chain of parents from `a`, without collecting it.
        let Some(vals) = self.values.get(axis) else {
            return a == b;
        };
        let mut cur = a;
        loop {
            if cur == b {
                return true;
            }
            match vals.get(cur) {
                Some(Some(parent)) => cur = parent,
                _ => return false,
            }
        }
    }

    fn overlap_declared(&self, axis: &str, a: &str, b: &str) -> bool {
        if self.overlaps.is_empty() {
            return false;
        }
        let aa = self.ancestors(axis, a);
        let bb = self.ancestors(axis, b);
        aa.iter().any(|x| {
            bb.iter().any(|y| {
                let (p, q) = if x < y { (x, y) } else { (y, x) };
                self.overlaps
                    .contains(&(axis.to_string(), p.clone(), q.clone()))
            })
        })
    }

    pub fn value_meet(&self, axis: &str, a: &str, b: &str) -> Option<String> {
        if a == b {
            return Some(a.to_string());
        }
        if self.value_within(axis, a, b) {
            return Some(a.to_string());
        }
        if self.value_within(axis, b, a) {
            return Some(b.to_string());
        }
        // Two plain values, neither within the other, meet only by a declared
        // overlap.
        if !a.contains(MEET) && !b.contains(MEET) && !self.overlap_declared(axis, a, b) {
            return None;
        }
        let parts_a: Vec<&str> = a.split(MEET).collect();
        let parts_b: Vec<&str> = b.split(MEET).collect();
        let all_overlap = parts_a.iter().all(|x| {
            parts_b.iter().all(|y| {
                self.value_within(axis, x, y)
                    || self.value_within(axis, y, x)
                    || self.overlap_declared(axis, x, y)
            })
        });
        if !all_overlap {
            return None;
        }
        let mut parts: Vec<&str> = parts_a.into_iter().chain(parts_b).collect();
        parts.sort();
        parts.dedup();
        // A part that contains another adds nothing: `gestation∩law` met with
        // `bio` stays `gestation∩law`, one region under one name.
        let all = parts.clone();
        parts.retain(|p| !all.iter().any(|q| q != p && self.value_within(axis, q, p)));
        Some(parts.join(&MEET.to_string()))
    }

    /// Context `c` lies within plane `p`: every constraint of `p` is met by `c`.
    pub fn plane_within(&self, c: &Plane, p: &Plane) -> bool {
        p.iter()
            .all(|(axis, v)| c.get(axis).is_some_and(|cv| self.value_within(axis, cv, v)))
    }

    pub fn strictly_within(&self, a: &Plane, b: &Plane) -> bool {
        self.plane_within(a, b) && !self.plane_within(b, a)
    }

    /// Intersection of two planes, or `None` if they are disjoint.
    pub fn plane_meet(&self, a: &Plane, b: &Plane) -> Option<Plane> {
        // Meet the shared axes first: most pairs are disjoint, and then
        // nothing is cloned.
        let mut shared = Vec::new();
        for (axis, vb) in b {
            if let Some(va) = a.get(axis) {
                shared.push((axis, self.value_meet(axis, va, vb)?));
            }
        }
        let mut out = a.clone();
        for (axis, vb) in b {
            if !a.contains_key(axis) {
                out.insert(axis.clone(), vb.clone());
            }
        }
        for (axis, v) in shared {
            out.insert(axis.clone(), v);
        }
        Some(out)
    }
}

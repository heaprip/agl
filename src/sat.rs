//! A CDCL satisfiability solver (`docs/impl/atlas.md` §7).
//!
//! Clauses over boolean variables; the solver finds values making every
//! clause true, or shows there are none. On a conflict it walks the reasons
//! of the forced values back to the first unique implication point, learns
//! the clause that rules the cause out and jumps back to where the cause
//! began (Marques-Silva and Sakallah, GRASP). Two literals of each clause
//! are watched, so a clause is looked at only when one of them turns false;
//! the next variable is the most active in recent conflicts, and the search
//! restarts on the Luby sequence, keeping what it learned (Chaff, MiniSat).
//! Nothing is random: ties go to the lower variable.

/// A literal: variable `v` is `2v`, its negation `2v + 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    pub fn pos(v: usize) -> Lit {
        Lit(2 * v as u32)
    }
    pub fn neg(v: usize) -> Lit {
        Lit(2 * v as u32 + 1)
    }
    pub fn var(self) -> usize {
        (self.0 / 2) as usize
    }
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
    fn negative(self) -> bool {
        self.0 & 1 == 1
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

const UNSET: u8 = 2;

#[derive(Default)]
pub struct Solver {
    clauses: Vec<Vec<Lit>>,
    watches: Vec<Vec<usize>>,
    value: Vec<u8>,
    level: Vec<usize>,
    reason: Vec<Option<usize>>,
    trail: Vec<Lit>,
    limits: Vec<usize>,
    head: usize,
    activity: Vec<f64>,
    bump: f64,
    phase: Vec<bool>,
    broken: bool,
    pub conflicts: usize,
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            bump: 1.0,
            ..Default::default()
        }
    }

    pub fn var(&mut self) -> usize {
        let v = self.value.len();
        self.value.push(UNSET);
        self.level.push(0);
        self.reason.push(None);
        self.activity.push(0.0);
        self.phase.push(false);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        v
    }

    fn lit(&self, l: Lit) -> u8 {
        match self.value[l.var()] {
            UNSET => UNSET,
            v => v ^ l.negative() as u8,
        }
    }

    fn assign(&mut self, l: Lit, reason: Option<usize>) {
        self.value[l.var()] = !l.negative() as u8;
        self.level[l.var()] = self.limits.len();
        self.reason[l.var()] = reason;
        self.trail.push(l);
    }

    /// Adds a clause; between searches, at the top level.
    pub fn add(&mut self, lits: &[Lit]) {
        self.backjump(0);
        let mut c: Vec<Lit> = lits.to_vec();
        c.sort();
        c.dedup();
        if c.windows(2).any(|w| w[0].var() == w[1].var()) || c.iter().any(|&l| self.lit(l) == 1) {
            return;
        }
        c.retain(|&l| self.lit(l) == UNSET);
        match c.len() {
            0 => self.broken = true,
            1 => {
                self.assign(c[0], None);
                if self.propagate().is_some() {
                    self.broken = true;
                }
            }
            _ => {
                self.attach(c);
            }
        }
    }

    fn attach(&mut self, c: Vec<Lit>) -> usize {
        let i = self.clauses.len();
        self.watches[c[0].not().0 as usize].push(i);
        self.watches[c[1].not().0 as usize].push(i);
        self.clauses.push(c);
        i
    }

    /// Forces every unit clause; the conflicting clause if one turns false.
    fn propagate(&mut self) -> Option<usize> {
        while self.head < self.trail.len() {
            let p = self.trail[self.head];
            self.head += 1;
            // Clauses watching ¬p, which has just turned false.
            let ws = std::mem::take(&mut self.watches[p.0 as usize]);
            let mut keep = Vec::with_capacity(ws.len());
            let mut conflict = None;
            let mut it = ws.into_iter();
            for ci in it.by_ref() {
                let false_lit = p.not();
                let c = &mut self.clauses[ci];
                if c[0] == false_lit {
                    c.swap(0, 1);
                }
                let first = c[0];
                if self.value[first.var()] != UNSET
                    && (self.value[first.var()] ^ first.negative() as u8) == 1
                {
                    keep.push(ci);
                    continue;
                }
                let mut moved = false;
                for k in 2..c.len() {
                    let l = c[k];
                    let v = self.value[l.var()];
                    if v == UNSET || (v ^ l.negative() as u8) == 1 {
                        c.swap(1, k);
                        let w = c[1].not().0 as usize;
                        self.watches[w].push(ci);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                keep.push(ci);
                match self.lit(first) {
                    0 => {
                        conflict = Some(ci);
                        break;
                    }
                    _ => self.assign(first, Some(ci)),
                }
            }
            keep.extend(it);
            let slot = &mut self.watches[p.0 as usize];
            keep.append(slot);
            *slot = keep;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// The learned clause, asserting literal first, and the level to jump to.
    fn analyze(&mut self, mut ci: usize) -> (Vec<Lit>, usize) {
        let mut seen = vec![false; self.value.len()];
        let mut learnt = vec![Lit(0)];
        let mut open = 0;
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();
        let here = self.limits.len();
        loop {
            let c = self.clauses[ci].clone();
            for &q in c.iter().skip(p.is_some() as usize) {
                let v = q.var();
                if !seen[v] && self.level[v] > 0 {
                    seen[v] = true;
                    self.activity[v] += self.bump;
                    if self.activity[v] > 1e100 {
                        self.activity.iter_mut().for_each(|a| *a *= 1e-100);
                        self.bump *= 1e-100;
                    }
                    if self.level[v] == here {
                        open += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            loop {
                index -= 1;
                if seen[self.trail[index].var()] {
                    break;
                }
            }
            let l = self.trail[index];
            seen[l.var()] = false;
            open -= 1;
            if open == 0 {
                learnt[0] = l.not();
                break;
            }
            p = Some(l);
            ci = self.reason[l.var()].unwrap();
            // The reason clause has `l` first.
            let c = &mut self.clauses[ci];
            if c[0] != l {
                let k = c.iter().position(|&x| x == l).unwrap();
                c.swap(0, k);
            }
        }
        let mut back = 0;
        if learnt.len() > 1 {
            let k = (1..learnt.len())
                .max_by_key(|&k| (self.level[learnt[k].var()], std::cmp::Reverse(k)))
                .unwrap();
            learnt.swap(1, k);
            back = self.level[learnt[1].var()];
        }
        (learnt, back)
    }

    fn backjump(&mut self, level: usize) {
        if self.limits.len() <= level {
            return;
        }
        let from = self.limits[level];
        for l in self.trail.drain(from..) {
            self.phase[l.var()] = !l.negative();
            self.value[l.var()] = UNSET;
            self.reason[l.var()] = None;
        }
        self.limits.truncate(level);
        self.head = self.trail.len();
    }

    fn pick(&self) -> Option<usize> {
        let mut best: Option<usize> = None;
        for v in 0..self.value.len() {
            if self.value[v] == UNSET && best.is_none_or(|b| self.activity[v] > self.activity[b]) {
                best = Some(v);
            }
        }
        best
    }

    /// Searches for values making every clause true; on success, `model`
    /// reads them until the next change.
    pub fn solve(&mut self) -> bool {
        if self.broken {
            return false;
        }
        self.backjump(0);
        if self.propagate().is_some() {
            self.broken = true;
            return false;
        }
        let mut restart = 1;
        let mut budget = luby(restart) * 64;
        loop {
            if let Some(ci) = self.propagate() {
                self.conflicts += 1;
                if self.limits.is_empty() {
                    self.broken = true;
                    return false;
                }
                let (learnt, back) = self.analyze(ci);
                self.backjump(back);
                if learnt.len() == 1 {
                    self.assign(learnt[0], None);
                } else {
                    let first = learnt[0];
                    let i = self.attach(learnt);
                    self.assign(first, Some(i));
                }
                self.bump /= 0.95;
                budget = budget.saturating_sub(1);
                continue;
            }
            if budget == 0 {
                restart += 1;
                budget = luby(restart) * 64;
                self.backjump(0);
                continue;
            }
            match self.pick() {
                None => return true,
                Some(v) => {
                    self.limits.push(self.trail.len());
                    let l = if self.phase[v] {
                        Lit::pos(v)
                    } else {
                        Lit::neg(v)
                    };
                    self.assign(l, None);
                }
            }
        }
    }

    /// The value of `v` in the model just found.
    pub fn model(&self, v: usize) -> bool {
        self.value[v] == 1
    }
}

/// The Luby sequence 1, 1, 2, 1, 1, 2, 4, …, from 1.
fn luby(i: usize) -> usize {
    let mut k = 1;
    while (1 << k) - 1 < i {
        k += 1;
    }
    if (1 << k) - 1 == i {
        1 << (k - 1)
    } else {
        luby(i - (1 << (k - 1)) + 1)
    }
}

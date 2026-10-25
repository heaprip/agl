//! Nesting labels: "A within B" read from numbers, not derived (H61).
//!
//! From edges "species → genus" the strongly connected components are found
//! (a cycle makes its members within each other), a spanning tree of the
//! components is chosen (the genus first by name), the components are
//! numbered in postorder (children by name), and each gets the merged
//! intervals of its own subtree and of every descendant in the graph: the
//! tree-plus-exceptions labelling of Agrawal, Borgida and Jagadish (SIGMOD
//! 1989). A is within B when A's number falls in one of B's intervals; the
//! relation is reflexive. Everything is ordered by name, so the labels do not
//! depend on the order of the edges.

/// A closed interval of postorder numbers.
pub type Interval = (u32, u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Labels {
    /// Sorted, distinct; a node's index is its rank by name.
    names: Vec<String>,
    /// node -> component; components are ranked by their first member.
    comp: Vec<u32>,
    /// component -> members, by name
    members: Vec<Vec<u32>>,
    /// component -> on a cycle (several members, or an edge to itself)
    cyclic: Vec<bool>,
    /// component -> postorder number
    num: Vec<u32>,
    /// postorder number -> component
    by_num: Vec<u32>,
    /// component -> sorted, disjoint, non-adjacent intervals
    iv: Vec<Vec<Interval>>,
}

impl Labels {
    /// Builds labels from (species, genus) edges.
    pub fn build<'a>(edges: impl IntoIterator<Item = (&'a str, &'a str)>) -> Self {
        let edges: Vec<(&str, &str)> = edges.into_iter().collect();
        let mut names: Vec<&str> = edges.iter().flat_map(|&(a, b)| [a, b]).collect();
        names.sort_unstable();
        names.dedup();
        let n = names.len();
        let at = |s: &str| names.binary_search(&s).expect("named in an edge") as u32;
        let mut parents = vec![Vec::new(); n];
        let mut self_loop = vec![false; n];
        for &(a, b) in &edges {
            if a == b {
                self_loop[at(a) as usize] = true;
            } else {
                parents[at(a) as usize].push(at(b));
            }
        }
        for v in &mut parents {
            v.sort_unstable();
            v.dedup();
        }

        // Components (Tarjan, iterative), then ranked by their first member.
        let raw = tarjan(&parents);
        let mut first: Vec<(u32, u32)> = Vec::new(); // (first member, raw id)
        let mut seen = vec![false; raw.iter().map(|&c| c as usize + 1).max().unwrap_or(0)];
        for (i, &c) in raw.iter().enumerate() {
            if !seen[c as usize] {
                seen[c as usize] = true;
                first.push((i as u32, c));
            }
        }
        let mut rank = vec![0u32; first.len()];
        for (r, &(_, c)) in first.iter().enumerate() {
            rank[c as usize] = r as u32;
        }
        let comp: Vec<u32> = raw.iter().map(|&c| rank[c as usize]).collect();
        let m = first.len();
        let mut members = vec![Vec::new(); m];
        for (i, &c) in comp.iter().enumerate() {
            members[c as usize].push(i as u32);
        }
        let cyclic: Vec<bool> = members
            .iter()
            .map(|ms| ms.len() > 1 || self_loop[ms[0] as usize])
            .collect();
        let mut cparents = vec![Vec::new(); m];
        let mut cchildren = vec![Vec::new(); m];
        for (i, ps) in parents.iter().enumerate() {
            let c = comp[i];
            for &p in ps {
                let d = comp[p as usize];
                if d != c {
                    cparents[c as usize].push(d);
                    cchildren[d as usize].push(c);
                }
            }
        }
        for v in cparents.iter_mut().chain(cchildren.iter_mut()) {
            v.sort_unstable();
            v.dedup();
        }

        // Children before parents (Kahn on the number of unprocessed children).
        let mut left: Vec<usize> = cchildren.iter().map(Vec::len).collect();
        let mut order: Vec<u32> = (0..m as u32).filter(|&c| left[c as usize] == 0).collect();
        let mut k = 0;
        while k < order.len() {
            let c = order[k] as usize;
            k += 1;
            for &p in &cparents[c] {
                left[p as usize] -= 1;
                if left[p as usize] == 0 {
                    order.push(p);
                }
            }
        }

        // Spanning tree: the genus first by name; postorder, children by name.
        let mut tree_children = vec![Vec::new(); m];
        for (c, ps) in cparents.iter().enumerate() {
            if let Some(&p) = ps.first() {
                tree_children[p as usize].push(c as u32);
            }
        }
        let mut num = vec![0u32; m];
        let mut low = vec![0u32; m];
        let mut next = 0u32;
        for root in (0..m as u32).filter(|&c| cparents[c as usize].is_empty()) {
            // (component, index of the next child to visit)
            let mut stack = vec![(root, 0usize)];
            low[root as usize] = next;
            while let Some(&mut (v, ref mut c)) = stack.last_mut() {
                if let Some(&ch) = tree_children[v as usize].get(*c) {
                    *c += 1;
                    low[ch as usize] = next;
                    stack.push((ch, 0));
                } else {
                    num[v as usize] = next;
                    next += 1;
                    stack.pop();
                }
            }
        }
        let mut by_num = vec![0u32; m];
        for (c, &x) in num.iter().enumerate() {
            by_num[x as usize] = c as u32;
        }

        let mut iv: Vec<Vec<Interval>> = vec![Vec::new(); m];
        for &c in &order {
            let c = c as usize;
            let mut all = vec![(low[c], num[c])];
            for &d in &cchildren[c] {
                all.extend_from_slice(&iv[d as usize]);
            }
            iv[c] = merge(all);
        }
        Labels {
            names: names.into_iter().map(str::to_string).collect(),
            comp,
            members,
            cyclic,
            num,
            by_num,
            iv,
        }
    }

    fn index(&self, name: &str) -> Option<usize> {
        self.names.binary_search_by(|s| s.as_str().cmp(name)).ok()
    }

    /// A node's rank by name: the number `name_at` reads back.
    pub fn node(&self, name: &str) -> Option<u32> {
        self.index(name).map(|i| i as u32)
    }

    pub fn name_at(&self, node: u32) -> &str {
        &self.names[node as usize]
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// All intervals of all components.
    pub fn interval_count(&self) -> usize {
        self.iv.iter().map(Vec::len).sum()
    }

    /// The postorder number of a node's component.
    pub fn number(&self, name: &str) -> Option<u32> {
        self.index(name).map(|i| self.num[self.comp[i] as usize])
    }

    pub fn intervals(&self, name: &str) -> Option<&[Interval]> {
        self.index(name)
            .map(|i| self.iv[self.comp[i] as usize].as_slice())
    }

    /// Is `a` on a cycle of edges (so that it reaches itself)?
    pub fn cyclic(&self, a: &str) -> bool {
        self.index(a)
            .is_some_and(|i| self.cyclic[self.comp[i] as usize])
    }

    /// Is `a` within `b`? Reflexive; a name in no edge is within itself only.
    pub fn within(&self, a: &str, b: &str) -> bool {
        if a == b {
            return true;
        }
        match (self.index(a), self.index(b)) {
            (Some(a), Some(b)) => contains(
                &self.iv[self.comp[b] as usize],
                self.num[self.comp[a] as usize],
            ),
            _ => false,
        }
    }

    /// Does a path of one edge or more lead from `a` to `b`?
    pub fn reaches(&self, a: &str, b: &str) -> bool {
        self.within(a, b) && (a != b || self.cyclic(a))
    }

    /// Everything within `b`, `b` included, by postorder number, then name.
    pub fn descendants(&self, b: &str) -> Vec<&str> {
        let Some(b) = self.index(b) else {
            return Vec::new();
        };
        self.iv[self.comp[b] as usize]
            .iter()
            .flat_map(|&(lo, hi)| lo..=hi)
            .flat_map(|x| &self.members[self.by_num[x as usize] as usize])
            .map(|&i| self.names[i as usize].as_str())
            .collect()
    }

    /// How many nodes are within `b`, `b` included.
    pub fn descendant_count(&self, b: &str) -> usize {
        self.index(b).map_or(0, |b| {
            self.iv[self.comp[b] as usize]
                .iter()
                .flat_map(|&(lo, hi)| lo..=hi)
                .map(|x| self.members[self.by_num[x as usize] as usize].len())
                .sum()
        })
    }

    /// Everything `a` is within, `a` included, by name.
    pub fn ancestors(&self, a: &str) -> Vec<&str> {
        let Some(i) = self.index(a) else {
            return Vec::new();
        };
        let x = self.num[self.comp[i] as usize];
        (0..self.len())
            .filter(|&b| contains(&self.iv[self.comp[b] as usize], x))
            .map(|b| self.names[b].as_str())
            .collect()
    }

    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.names.iter().map(String::as_str)
    }
}

/// Strongly connected components of `next` (Tarjan), without recursion.
/// Visits nodes and their successors in index order, so the result depends
/// only on the graph.
fn tarjan(next: &[Vec<u32>]) -> Vec<u32> {
    const NONE: u32 = u32::MAX;
    let n = next.len();
    let mut index = vec![NONE; n];
    let mut low = vec![0u32; n];
    let mut on = vec![false; n];
    let mut comp = vec![NONE; n];
    let mut stack: Vec<u32> = Vec::new();
    let mut counter = 0u32;
    let mut comps = 0u32;
    for root in 0..n as u32 {
        if index[root as usize] != NONE {
            continue;
        }
        let mut call: Vec<(u32, usize)> = vec![(root, 0)];
        index[root as usize] = counter;
        low[root as usize] = counter;
        counter += 1;
        stack.push(root);
        on[root as usize] = true;
        while let Some(&mut (v, ref mut k)) = call.last_mut() {
            let v_ = v as usize;
            if let Some(&w) = next[v_].get(*k) {
                *k += 1;
                let w_ = w as usize;
                if index[w_] == NONE {
                    index[w_] = counter;
                    low[w_] = counter;
                    counter += 1;
                    stack.push(w);
                    on[w_] = true;
                    call.push((w, 0));
                } else if on[w_] {
                    low[v_] = low[v_].min(index[w_]);
                }
            } else {
                call.pop();
                if let Some(&(u, _)) = call.last() {
                    low[u as usize] = low[u as usize].min(low[v_]);
                }
                if low[v_] == index[v_] {
                    loop {
                        let w = stack.pop().expect("tarjan stack");
                        on[w as usize] = false;
                        comp[w as usize] = comps;
                        if w == v {
                            break;
                        }
                    }
                    comps += 1;
                }
            }
        }
    }
    comp
}

fn merge(mut all: Vec<Interval>) -> Vec<Interval> {
    all.sort_unstable();
    let mut out: Vec<Interval> = Vec::with_capacity(all.len());
    for (lo, hi) in all {
        match out.last_mut() {
            Some(last) if lo <= last.1 + 1 => last.1 = last.1.max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

fn contains(iv: &[Interval], x: u32) -> bool {
    let k = iv.partition_point(|&(lo, _)| lo <= x);
    k > 0 && iv[k - 1].1 >= x
}

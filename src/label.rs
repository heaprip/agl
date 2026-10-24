//! Nesting labels: "A within B" read from numbers, not derived (H61, step 1).
//!
//! From edges "species → genus" a spanning tree is chosen (the genus first by
//! name), its nodes are numbered in postorder (children by name), and each
//! node gets the merged intervals of its own subtree and of every descendant
//! in the graph: the tree-plus-exceptions labelling of Agrawal, Borgida and
//! Jagadish (SIGMOD 1989). A is within B when A's number falls in one of B's
//! intervals; the relation is reflexive. Everything is ordered by name, so
//! the labels do not depend on the order of the edges. A cycle is an error.

/// A closed interval of postorder numbers.
pub type Interval = (u32, u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Labels {
    /// Sorted, distinct; a node's index is its rank by name.
    names: Vec<String>,
    /// index -> postorder number
    num: Vec<u32>,
    /// postorder number -> index
    by_num: Vec<u32>,
    /// index -> sorted, disjoint, non-adjacent intervals
    iv: Vec<Vec<Interval>>,
}

impl Labels {
    /// Builds labels from (species, genus) edges.
    pub fn build<'a>(edges: impl IntoIterator<Item = (&'a str, &'a str)>) -> Result<Self, String> {
        let edges: Vec<(&str, &str)> = edges.into_iter().collect();
        let mut names: Vec<&str> = edges.iter().flat_map(|&(a, b)| [a, b]).collect();
        names.sort_unstable();
        names.dedup();
        let n = names.len();
        let at = |s: &str| names.binary_search(&s).expect("named in an edge") as u32;
        let mut parents = vec![Vec::new(); n];
        let mut children = vec![Vec::new(); n];
        for &(a, b) in &edges {
            if a == b {
                return Err(format!("`{a}` is within itself"));
            }
            parents[at(a) as usize].push(at(b));
            children[at(b) as usize].push(at(a));
        }
        for v in parents.iter_mut().chain(children.iter_mut()) {
            v.sort_unstable();
            v.dedup();
        }

        // Children before parents (Kahn on the number of unprocessed children).
        let mut left: Vec<usize> = children.iter().map(Vec::len).collect();
        let mut order: Vec<u32> = (0..n as u32).filter(|&i| left[i as usize] == 0).collect();
        let mut k = 0;
        while k < order.len() {
            let i = order[k] as usize;
            k += 1;
            for &p in &parents[i] {
                left[p as usize] -= 1;
                if left[p as usize] == 0 {
                    order.push(p);
                }
            }
        }
        if order.len() < n {
            let i = (0..n).find(|&i| left[i] > 0).expect("a node on a cycle");
            return Err(format!("cycle through `{}`", names[i]));
        }

        // Spanning tree: the genus first by name; postorder, children by name.
        let mut tree_children = vec![Vec::new(); n];
        for (i, ps) in parents.iter().enumerate() {
            if let Some(&p) = ps.first() {
                tree_children[p as usize].push(i as u32);
            }
        }
        let mut num = vec![0u32; n];
        let mut low = vec![0u32; n];
        let mut next = 0u32;
        for root in (0..n as u32).filter(|&i| parents[i as usize].is_empty()) {
            // (node, index of the next child to visit)
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
        let mut by_num = vec![0u32; n];
        for (i, &x) in num.iter().enumerate() {
            by_num[x as usize] = i as u32;
        }

        let mut iv: Vec<Vec<Interval>> = vec![Vec::new(); n];
        for &i in &order {
            let i = i as usize;
            let mut all = vec![(low[i], num[i])];
            for &c in &children[i] {
                all.extend_from_slice(&iv[c as usize]);
            }
            iv[i] = merge(all);
        }
        Ok(Labels {
            names: names.into_iter().map(str::to_string).collect(),
            num,
            by_num,
            iv,
        })
    }

    fn index(&self, name: &str) -> Option<usize> {
        self.names.binary_search_by(|s| s.as_str().cmp(name)).ok()
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// All intervals of all nodes.
    pub fn interval_count(&self) -> usize {
        self.iv.iter().map(Vec::len).sum()
    }

    pub fn number(&self, name: &str) -> Option<u32> {
        self.index(name).map(|i| self.num[i])
    }

    pub fn intervals(&self, name: &str) -> Option<&[Interval]> {
        self.index(name).map(|i| self.iv[i].as_slice())
    }

    /// Is `a` within `b`? Reflexive; a name in no edge is within itself only.
    pub fn within(&self, a: &str, b: &str) -> bool {
        if a == b {
            return true;
        }
        match (self.index(a), self.index(b)) {
            (Some(a), Some(b)) => contains(&self.iv[b], self.num[a]),
            _ => false,
        }
    }

    /// Everything within `b`, `b` included, by postorder number.
    pub fn descendants(&self, b: &str) -> Vec<&str> {
        let Some(b) = self.index(b) else {
            return Vec::new();
        };
        self.iv[b]
            .iter()
            .flat_map(|&(lo, hi)| lo..=hi)
            .map(|x| self.names[self.by_num[x as usize] as usize].as_str())
            .collect()
    }

    /// How many nodes are within `b`, `b` included.
    pub fn descendant_count(&self, b: &str) -> usize {
        self.index(b).map_or(0, |b| {
            self.iv[b]
                .iter()
                .map(|&(lo, hi)| (hi - lo + 1) as usize)
                .sum()
        })
    }

    /// Everything `a` is within, `a` included, by name.
    pub fn ancestors(&self, a: &str) -> Vec<&str> {
        let Some(i) = self.index(a) else {
            return Vec::new();
        };
        let x = self.num[i];
        (0..self.len())
            .filter(|&b| contains(&self.iv[b], x))
            .map(|b| self.names[b].as_str())
            .collect()
    }

    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.names.iter().map(String::as_str)
    }
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

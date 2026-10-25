//! Exact finite sets backed by dense words.
//!
//! This is only a representation primitive.  The meaning of an index and
//! the plane in which a set is valid belong to the caller.

/// An exact finite set as machine words.
///
/// Sets participating in one operation must have been built for the same
/// universe.  The tuple field stays public for bulk, word-at-a-time kernels;
/// semantic code should prefer the methods below.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct DenseSet(pub Vec<u64>);

impl DenseSet {
    pub fn none(n: usize) -> Self {
        DenseSet(vec![0; n.div_ceil(64).max(1)])
    }

    pub fn all(n: usize) -> Self {
        let mut words = vec![u64::MAX; n.div_ceil(64).max(1)];
        let tail = n % 64;
        if tail != 0 {
            *words.last_mut().unwrap() = (1u64 << tail) - 1;
        } else if n == 0 {
            words[0] = 0;
        }
        DenseSet(words)
    }

    pub fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }

    pub fn remove(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }

    pub fn contains(&self, i: usize) -> bool {
        self.0[i / 64] >> (i % 64) & 1 == 1
    }

    pub fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }

    pub fn and(&self, other: &Self) -> Self {
        self.assert_compatible(other);
        DenseSet(self.0.iter().zip(&other.0).map(|(a, b)| a & b).collect())
    }

    pub fn or(&self, other: &Self) -> Self {
        self.assert_compatible(other);
        DenseSet(self.0.iter().zip(&other.0).map(|(a, b)| a | b).collect())
    }

    pub fn minus(&self, other: &Self) -> Self {
        self.assert_compatible(other);
        DenseSet(self.0.iter().zip(&other.0).map(|(a, b)| a & !b).collect())
    }

    pub fn within(&self, other: &Self) -> bool {
        self.assert_compatible(other);
        self.0.iter().zip(&other.0).all(|(a, b)| a & !b == 0)
    }

    pub fn is_empty(&self) -> bool {
        self.0.iter().all(|&word| word == 0)
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0
            .iter()
            .enumerate()
            .flat_map(|(word_index, &word)| SetBits {
                base: word_index * 64,
                word,
            })
    }

    fn assert_compatible(&self, other: &Self) {
        assert_eq!(
            self.0.len(),
            other.0.len(),
            "sets belong to different finite universes"
        );
    }
}

struct SetBits {
    base: usize,
    word: u64,
}

impl Iterator for SetBits {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.word == 0 {
            return None;
        }
        let bit = self.word.trailing_zeros() as usize;
        self.word &= self.word - 1;
        Some(self.base + bit)
    }
}

#[cfg(test)]
mod tests {
    use super::DenseSet;

    #[test]
    fn exact_tail_and_operations() {
        let all = DenseSet::all(65);
        assert_eq!(all.count(), 65);
        assert!(all.contains(64));
        assert_eq!(all.iter().last(), Some(64));

        let mut a = DenseSet::none(65);
        a.insert(1);
        a.insert(64);
        let mut b = DenseSet::none(65);
        b.insert(64);

        assert_eq!(a.and(&b).iter().collect::<Vec<_>>(), vec![64]);
        assert_eq!(a.minus(&b).iter().collect::<Vec<_>>(), vec![1]);
        assert_eq!(b.or(&a), a);
        assert!(b.within(&a));
        assert!(!a.within(&b));

        a.remove(1);
        assert_eq!(a, b);
    }
}

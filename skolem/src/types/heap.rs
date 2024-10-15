use std::{
    cell::RefCell,
    collections::VecDeque,
    ops::{AddAssign, DivAssign, MulAssign, SubAssign},
    rc::{Rc, Weak},
};

/// Max-Priority Queue, implemented as a binary heap
#[derive(Debug, Clone)]
pub struct Heap<K, V> {
    heap: Vec<(K, V, StrongIndex)>,
    size: usize,
}

pub struct IntoIter<K, V> {
    pq: Heap<K, V>,
}

#[derive(Debug, Clone)]
pub struct Index(Weak<RefCell<usize>>);

#[derive(Debug, Clone)]
struct StrongIndex(Rc<RefCell<usize>>);

fn parent_idx(i: usize) -> usize {
    (i + 1) / 2 - 1
}

fn left_child_idx(i: usize) -> usize {
    2 * (i + 1) - 1
}

fn right_child_idx(i: usize) -> usize {
    2 * (i + 1)
}

impl<K: Ord, V> std::iter::Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.pq.pop_max()
    }
}

impl<K, V> Heap<K, V> {
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl<K: Ord, V> Heap<K, V> {
    pub fn new() -> Self {
        Heap {
            heap: Vec::with_capacity(64),
            size: 0,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Heap {
            heap: Vec::with_capacity(capacity),
            size: 0,
        }
    }

    pub fn peek(&self, idx: Index) -> Option<(&K, &V)> {
        idx.0
            .upgrade()
            .and_then(|i| self.heap.get(*i.borrow()).map(|(k, v, _)| (k, v)))
    }

    pub fn delete(&mut self, idx: Index) -> Option<(K, V)> {
        let i = *idx.0.upgrade()?.borrow();
        if i >= self.size {
            return None;
        } else if i == self.size - 1 {
            self.size -= 1;
            return self.heap.pop().map(|(k, v, _)| (k, v));
        }
        self.swap(i, self.size - 1);
        let mkv = self.heap.pop().map(|(k, v, _)| (k, v));
        self.size -= 1;
        let (k, _, _) = &self.heap[i];
        if self
            .left_child(i)
            .is_some_and(|(_, w)| w > k || self.right_child(i).map_or(false, |(_, w)| w > k))
        {
            self.down_heap(i);
        } else {
            self.up_heap(i);
        }
        mkv
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// Maps all the priority by a given map;
    /// Monotonicity of the map is not checked!
    pub fn map_monotonic<F>(&mut self, f: F)
    where
        F: Fn(&mut K),
    {
        for (ref mut k, _, _) in self.heap.iter_mut() {
            f(k)
        }
    }

    pub fn push(&mut self, key: K, value: V) -> Index {
        let idx = self.size;
        let i = Rc::new(RefCell::new(idx));
        self.heap.push((key, value, StrongIndex(i.clone())));
        self.size += 1;

        self.up_heap(idx);
        Index(Rc::downgrade(&i))
    }

    pub fn pop_max(&mut self) -> Option<(K, V)> {
        if self.size == 0 {
            return None;
        } else if self.size == 1 {
            self.size = 0;
            return self.heap.pop().map(|(k, v, _)| (k, v));
        }

        let last = self.size - 1;
        self.swap(0, last);
        let ret = self.heap.pop();
        self.size -= 1;

        self.down_heap(0);

        ret.map(|(k, v, _)| (k, v))
    }

    pub fn peek_max(&self) -> Option<(&K, &V)> {
        self.heap.first().map(|(k, v, _)| (k, v))
    }

    fn up_heap(&mut self, mut i: usize) -> usize {
        while let Some((j, parent)) = self.parent(i) {
            let me = &self.heap[i].0;
            if me <= parent {
                break;
            } else {
                self.swap(i, j);
                i = j;
            }
        }
        i
    }

    fn parent(&self, i: usize) -> Option<(usize, &K)> {
        if i == 0 {
            None
        } else {
            let pidx = parent_idx(i);
            self.heap.get(pidx).map(|(k, _, _)| (pidx, k))
        }
    }

    fn left_child(&self, i: usize) -> Option<(usize, &K)> {
        let lidx = left_child_idx(i);
        self.heap.get(lidx).map(|(k, _, _)| (lidx, k))
    }

    fn right_child(&self, i: usize) -> Option<(usize, &K)> {
        let ridx = right_child_idx(i);
        self.heap.get(ridx).map(|(k, _, _)| (ridx, k))
    }

    fn swap(&mut self, i: usize, j: usize) {
        if i != j {
            self.heap.swap(i, j);
            self.heap[i].2 .0.swap(&self.heap[j].2 .0);
        }
    }

    fn down_heap(&mut self, i: usize) -> usize {
        let mut is = VecDeque::from([(i, true)]);
        let mut dest = i;
        while let Some((i, to_update)) = is.pop_front() {
            let me = &self.heap[i].0;

            if let Some((j, left)) = self.left_child(i) {
                if me >= left {
                    if let Some((k, right)) = self.right_child(i) {
                        if me < right {
                            self.swap(i, k);
                            is.push_front((k, to_update));
                            is.push_back((i, false));
                            if to_update {
                                dest = k
                            }
                        }
                    }
                } else {
                    self.swap(i, j);
                    is.push_front((j, to_update));
                    is.push_back((i, false));
                    if to_update {
                        dest = j
                    }
                }
            }
        }
        dest
    }
}

impl<K: MulAssign + Ord + Copy + From<f64>, V> Heap<K, V> {
    pub fn scale_priority(&mut self, factor: f64) {
        if factor < 0.0 {
            panic!("factor must be non-negative");
        }
        self.map_monotonic(|k| *k *= factor.into());
    }
}

impl<K: AddAssign + Ord + Copy, V> Heap<K, V> {
    pub fn increase_priority(&mut self, factor: K) {
        self.map_monotonic(|k| *k += factor);
    }
}

impl<K: MulAssign + Ord + Copy + From<f64>, V> MulAssign<f64> for Heap<K, V> {
    fn mul_assign(&mut self, rhs: f64) {
        self.scale_priority(rhs);
    }
}

impl<K: AddAssign + Ord + Copy, V> AddAssign<K> for Heap<K, V> {
    fn add_assign(&mut self, rhs: K) {
        self.increase_priority(rhs);
    }
}

impl<K: SubAssign + Ord + Copy, V> SubAssign<K> for Heap<K, V> {
    fn sub_assign(&mut self, rhs: K) {
        self.map_monotonic(|k| *k -= rhs);
    }
}

impl<K: DivAssign + Ord + Copy, V> DivAssign<K> for Heap<K, V> {
    fn div_assign(&mut self, rhs: K) {
        self.map_monotonic(|k| *k /= rhs);
    }
}

impl<K: Ord, V> Default for Heap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord, V> IntoIterator for Heap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { pq: self }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_push_pop_01() {
        let mut input = vec![3, 1, 99, 2, 4, 5];
        let mut pq = Heap::new();
        for i in input.iter() {
            pq.push(*i, *i);
        }
        input.sort_by_key(|i| -i);
        for i in input {
            assert_eq!(pq.pop_max(), Some((i, i)));
        }
        assert!(pq.pop_max().is_none());
    }

    #[test]
    fn test_push_delete_01() {
        let input = vec![3, 1, 99, 2, 4, 5];
        let mut pq = Heap::new();
        let mut idxs = HashMap::new();
        for i in input {
            let j = pq.push(i, i);
            idxs.insert(i, j);
        }
        for (i, idx) in idxs {
            assert_eq!(pq.delete(idx), Some((i, i)));
        }
        assert!(pq.pop_max().is_none());
    }
}

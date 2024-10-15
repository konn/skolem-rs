use super::heap::*;
use core::hash::Hash;
use std::{
    collections::HashMap,
    ops::{AddAssign, MulAssign, SubAssign},
};

pub struct PrioritySearchQueue<K, P, A> {
    queue: Heap<P, K>,
    dic: HashMap<K, (A, Index)>,
}

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    K: Eq + Hash + Clone,
    P: Ord + Copy,
{
    pub fn new() -> Self {
        PrioritySearchQueue {
            queue: Heap::new(),
            dic: HashMap::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    pub fn len(&self) -> usize {
        self.dic.len()
    }
}

impl<K, P, A> Default for PrioritySearchQueue<K, P, A>
where
    K: Eq + Hash + Clone,
    P: Ord + Copy,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    K: Hash + Eq,
    P: Ord + Copy,
{
    pub fn delete(&mut self, key: &K) -> Option<(P, A)> {
        self.dic.remove(key).map(|(value, idx)| {
            let (p, _) = self.queue.delete(idx).unwrap();
            (p, value)
        })
    }
}

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    P: Ord,
    K: Clone + Hash + Eq,
{
    pub fn push(&mut self, key: K, priority: P, value: A) {
        let idx = self.queue.push(priority, key.clone());
        self.dic.insert(key, (value, idx));
    }

    pub fn pop_max(&mut self) -> Option<(K, P, A)> {
        self.queue
            .pop_max()
            .map(|(weight, key)| (key.clone(), weight, self.dic.remove(&key).unwrap().0))
    }

    pub fn peek_max(&self) -> Option<(&K, &P, &A)> {
        self.queue
            .peek_max()
            .map(|(weight, key)| (key, weight, &self.dic[key].0))
    }

    pub fn remove(&mut self, key: K) -> Option<(P, A)> {
        self.dic.remove(&key).map(|(value, idx)| {
            let (p, _) = self.queue.delete(idx).unwrap();
            (p, value)
        })
    }
}

impl<K, P, A> MulAssign<f64> for PrioritySearchQueue<K, P, A>
where
    P: Ord + From<f64> + MulAssign + Copy,
{
    fn mul_assign(&mut self, rhs: f64) {
        self.queue *= rhs;
    }
}

impl<K, P, A> AddAssign<P> for PrioritySearchQueue<K, P, A>
where
    P: Ord + From<f64> + AddAssign + Copy,
{
    fn add_assign(&mut self, rhs: P) {
        self.queue += rhs;
    }
}

impl<K, P, A> SubAssign<P> for PrioritySearchQueue<K, P, A>
where
    P: Ord + From<f64> + SubAssign + Copy,
{
    fn sub_assign(&mut self, rhs: P) {
        self.queue -= rhs;
    }
}

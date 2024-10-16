use super::heap::*;
use core::hash::Hash;
use std::{
    collections::{hash_map, HashMap},
    ops::{Add, AddAssign, DivAssign, MulAssign, SubAssign},
};

pub struct PrioritySearchQueue<K, P, A> {
    queue: Heap<P, K>,
    dic: HashMap<K, (A, Index)>,
}

pub struct Entry<'a, K, P, V> {
    inner: hash_map::Entry<'a, K, (V, Index)>,
    table: &'a mut Heap<P, K>,
}

impl<K, P, V> Entry<'_, K, P, V> {
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        let Entry { inner, table } = self;
        Entry {
            inner: inner.and_modify(|(k, _)| f(k)),
            table,
        }
    }
}

impl<K, P, V> AddAssign<P> for Entry<'_, K, P, V>
where
    P: PartialOrd + Add<Output = P> + Copy,
    V: Clone,
{
    fn add_assign(&mut self, rhs: P) {
        let Entry { inner, table } = self;
        match inner {
            hash_map::Entry::Occupied(ref mut entry) => {
                let (v, idx) = entry.get();
                if let Some((p, k)) = table.delete(idx.clone()) {
                    let idx = table.push(p + rhs, k);
                    entry.insert((v.clone(), idx));
                }
            }
            hash_map::Entry::Vacant(_) => {}
        }
    }
}

impl<K, P, V> PrioritySearchQueue<K, P, V>
where
    K: Eq + Hash + Clone,
    P: PartialOrd + Copy,
{
    pub fn new() -> Self {
        PrioritySearchQueue {
            queue: Heap::new(),
            dic: HashMap::new(),
        }
    }

    /// Iterates over the keys and values _regardless of_ the priority.
    pub fn key_values_unsorted(&self) -> impl Iterator<Item = (&K, &P, &V)> {
        self.dic
            .iter()
            .map(|(k, (v, i))| (k, self.queue.peek(i).unwrap().0, v))
    }

    pub fn size(&self) -> usize {
        self.queue.size()
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, P, V> {
        let entry = self.dic.entry(key);
        let PrioritySearchQueue {
            queue: ref mut table,
            ..
        } = self;
        Entry {
            inner: entry,
            table,
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        PrioritySearchQueue {
            queue: Heap::with_capacity(capacity),
            dic: HashMap::with_capacity(capacity),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    pub fn len(&self) -> usize {
        self.dic.len()
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &P, &mut V) -> bool,
    {
        self.dic.retain(|k, (v, i)| {
            let p = self.queue.peek(i).unwrap().0;
            let hold = f(k, p, v);
            if !hold {
                self.queue.delete(i.clone());
            }
            hold
        });
    }
}

impl<K, P, A> FromIterator<(K, P, A)> for PrioritySearchQueue<K, P, A>
where
    K: Eq + Hash + Clone,
    P: PartialOrd + Copy,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, P, A)>,
    {
        let mut queue = Self::new();
        for (k, p, a) in iter.into_iter() {
            queue.push(k, p, a);
        }
        queue
    }
}

impl<K, P, A> Default for PrioritySearchQueue<K, P, A>
where
    K: Eq + Hash + Clone,
    P: PartialOrd + Copy,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    K: Hash + Eq,
    P: PartialOrd + Copy,
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
    P: PartialOrd,
    K: Clone + Hash + Eq,
{
    pub fn push(&mut self, key: K, priority: P, value: A) {
        let idx = self.queue.push(priority, key.clone());
        if let Some((_, idx)) = self.dic.insert(key, (value, idx)) {
            self.queue.delete(idx);
        }
    }

    pub fn pop_max(&mut self) -> Option<(K, P, A)> {
        self.queue
            .pop_max()
            .map(|(weight, key)| (key.clone(), weight, self.dic.remove(&key).unwrap().0))
    }

    pub fn get(&self, k: &K) -> Option<(&P, &A)> {
        self.dic.get(k).map(|(x, i)| {
            let (p, _) = self.queue.peek(i).unwrap();
            (p, x)
        })
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
    P: PartialOrd + From<f64> + MulAssign + Copy,
{
    fn mul_assign(&mut self, rhs: f64) {
        self.queue *= rhs;
    }
}
impl<K, P, A> DivAssign<f64> for PrioritySearchQueue<K, P, A>
where
    P: PartialOrd + From<f64> + DivAssign + Copy,
{
    fn div_assign(&mut self, rhs: f64) {
        self.queue /= rhs.into();
    }
}

impl<K, P, A> AddAssign<P> for PrioritySearchQueue<K, P, A>
where
    P: PartialOrd + From<f64> + AddAssign + Copy,
{
    fn add_assign(&mut self, rhs: P) {
        self.queue += rhs;
    }
}

impl<K, P, A> SubAssign<P> for PrioritySearchQueue<K, P, A>
where
    P: PartialOrd + From<f64> + SubAssign + Copy,
{
    fn sub_assign(&mut self, rhs: P) {
        self.queue -= rhs;
    }
}

pub struct IntoIter<K, P, V>(PrioritySearchQueue<K, P, V>);

impl<K, P, V> Iterator for IntoIter<K, P, V>
where
    P: PartialOrd,
    K: Clone + Hash + Eq,
{
    type Item = (K, P, V);
    fn next(&mut self) -> Option<(K, P, V)> {
        self.0.pop_max()
    }
}

impl<K: Hash + Eq, P: PartialOrd, V> IntoIterator for PrioritySearchQueue<K, P, V>
where
    P: PartialOrd,
    K: Clone + Hash + Eq,
{
    type Item = (K, P, V);
    type IntoIter = IntoIter<K, P, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

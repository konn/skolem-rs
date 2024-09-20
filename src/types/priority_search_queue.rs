use core::hash::Hash;
use std::{
    cmp::Ordering,
    collections::{BinaryHeap, HashMap},
};

struct Weighted<P, A> {
    weight: P,
    entry: A,
}

impl<P: Eq, A> Eq for Weighted<P, A> {}
impl<P: PartialEq, A> PartialEq for Weighted<P, A> {
    fn eq(&self, other: &Self) -> bool {
        self.weight == other.weight
    }
}

impl<P: Ord, A> PartialOrd for Weighted<P, A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<P: Ord, A> Ord for Weighted<P, A> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight.cmp(&other.weight)
    }
}

pub struct PrioritySearchQueue<K, P, A> {
    queue: BinaryHeap<Weighted<P, K>>,
    dic: HashMap<K, A>,
}

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    K: Eq + Hash + Clone,
    P: Ord + Copy,
{
    pub fn new() -> Self {
        PrioritySearchQueue {
            queue: BinaryHeap::new(),
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

impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    K: Hash + Eq,
    P: Ord + Copy,
{
    pub fn delete(&mut self, key: &K) -> Option<(P, A)> {
        self.dic.remove(key).map(|value| {
            let mut prio: Option<P> = None;
            self.queue.retain(|Weighted { entry, weight }| {
                if entry != key {
                    prio = Some(*weight);
                    false
                } else {
                    true
                }
            });
            (prio.unwrap(), value)
        })
    }
}
impl<K, P, A> PrioritySearchQueue<K, P, A>
where
    P: Ord,
    K: Clone + Hash + Eq,
{
    pub fn push(&mut self, key: K, priority: P, value: A) {
        self.dic.insert(key.clone(), value);
        self.queue.push(Weighted {
            weight: priority,
            entry: key,
        });
    }
    pub fn pop(&mut self) -> Option<(K, P, A)> {
        self.queue.pop().map(|Weighted { weight, entry }| {
            (entry.clone(), weight, self.dic.remove(&entry).unwrap())
        })
    }
}

use crate::types::*;
use itertools::Itertools;
use priority_search_queue::PrioritySearchQueue;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::hash::Hash;
use std::mem;
use std::{
    cell::{RefCell, RefMut},
    collections::{HashMap, HashSet, VecDeque},
    iter,
    ops::{Add, AddAssign, Neg, Not},
    rc::{Rc, Weak},
};

use crate::utils::*;
use Literal::*;

#[derive(Debug)]
enum Watchers {
    NextWatch(usize),
    Satisfied(usize),
}

#[derive(Debug, Clone)]
struct CDCLLit {
    lit: Literal,
    var: VarRef,
}

impl Neg for CDCLLit {
    type Output = Self;

    fn neg(self) -> Self::Output {
        CDCLLit {
            lit: -self.lit,
            var: self.var,
        }
    }
}

impl Not for CDCLLit {
    type Output = Self;

    fn not(self) -> Self {
        CDCLLit {
            lit: !self.lit,
            var: self.var,
        }
    }
}

impl PartialEq for CDCLLit {
    fn eq(&self, other: &Self) -> bool {
        self.lit == other.lit
    }
}

impl Eq for CDCLLit {}

impl Hash for CDCLLit {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.lit.hash(state);
    }
}

impl CDCLLit {
    pub fn eval(&self) -> Option<bool> {
        self.var
            .borrow()
            .value
            .as_ref()
            .map(|v| self.lit.eval(v.value))
    }

    pub fn raw_var(&self) -> Var {
        self.lit.var()
    }
}

#[derive(Debug)]
struct CDCLClause {
    // Invariant (a): at most one of b or -b may occur in literals.
    // Invaliant (b): lits is non-empty.
    lits: Vec<CDCLLit>,
    // Invariant (c): # of watching literals must remain the same.
    // Invariant (d): Exactly one of the followings must hold:
    //      (Case A): All watched literals are indeterminate,
    //      (Case B): At least one watched literal is true, or
    //      (Case C): All watched literals are false.
    watching1: usize,
    watching2: Option<usize>,
}

#[derive(Debug, Clone)]
enum ClauseLitState {
    Unit(CDCLLit),
    Conflict(CDCLLit),
    Satisfied,
}

impl CDCLClause {
    fn get(&self, i: usize) -> Literal {
        self.lits[i].lit
    }

    fn snapshot(&self) -> ClauseSnapshot {
        ClauseSnapshot {
            lits: self
                .lits
                .iter()
                .enumerate()
                .map(|(i, l)| ClauseSnapshotLit {
                    lit: l.lit,
                    state: l.eval(),
                    watched: i == self.watching1 || Some(i) == self.watching2,
                })
                .collect(),
        }
    }

    fn get_var_mut(&mut self, i: usize) -> RefMut<CDCLVar> {
        self.lits[i].var.borrow_mut()
    }

    fn get_watch1_lit(&self) -> Literal {
        self.get(self.watching1)
    }

    fn get_watch1(&self) -> &CDCLLit {
        self.lits.get(self.watching1).unwrap()
    }

    fn get_watch2_lit(&self) -> Option<Literal> {
        self.watching2.map(|i| self.get(i))
    }

    fn get_watch2(&self) -> Option<&CDCLLit> {
        self.watching2.map(|i| self.lits.get(i).unwrap())
    }

    fn eval(&self) -> Option<bool> {
        let mut val = Some(false);
        for l in &self.lits {
            match l.eval() {
                Some(true) => return Some(true),
                opt => val = opt_or(val, opt),
            }
        }
        val
    }

    fn watcher_candidate(&self) -> Option<Watchers> {
        use Watchers::*;
        let mut new_watcher = None;
        for (i, l) in self.lits.iter().enumerate() {
            if i == self.watching1 || Some(i) == self.watching2 {
                continue;
            }
            match l.eval() {
                None => {
                    new_watcher.get_or_insert(i);
                    break;
                }
                Some(true) => {
                    return Some(Satisfied(i));
                }
                Some(false) => continue,
            }
        }
        debug_assert!(
            new_watcher.map_or(true, |i| i != self.watching1 && Some(i) != self.watching2)
        );
        new_watcher.map(Watchers::NextWatch)
    }

    fn last_definite_watched(&self) -> &CDCLLit {
        [self.get_watch1()]
            .iter()
            .chain(self.get_watch2().iter())
            .max_by_key(|l| {
                l.var
                    .borrow()
                    .value
                    .as_ref()
                    .map(|v| (v.decision_level.0, v.decision_step.0))
                    .unwrap()
            })
            .unwrap()
    }
}

trait ClauseLike {
    fn find_unit(&mut self) -> Option<ClauseLitState>;

    fn propagate(&mut self, lit: &mut CDCLLit) -> Option<ClauseLitState>;

    fn switch_watcher_to(&mut self, w: Watcher, l: usize);
}

impl ClauseLike for ClauseRef {
    fn switch_watcher_to(&mut self, w: Watcher, l: usize) {
        let mut this = self.borrow_mut();
        debug_assert!(
            this.watching1 != l && this.watching2 != Some(l),
            "New watcher must be different to the existing ones!"
        );
        let watcher = match w {
            Watcher1 => &mut this.watching1,
            Watcher2 => this.watching2.as_mut().unwrap(),
        };
        let old = mem::replace(watcher, l);
        debug_assert!(*watcher == l, "Watcher must be set properly!");
        this.get_var_mut(old).remove_watcher(self);
        this.get_var_mut(l).add_watcher(Rc::downgrade(self));
    }

    fn find_unit(&mut self) -> Option<ClauseLitState> {
        use ClauseLitState::*;

        let (watcher, new_lit, satisfied) = {
            let this = self.borrow();
            let l1 = this.get_watch1();
            if let Some(l2) = this.get_watch2() {
                // Having two watched literals.
                match l1.eval() {
                    Some(true) => return Some(Satisfied),
                    Some(false) => {
                        // Unsatisfiable literal in Watched #1: find next available literal for watched1
                        if let Some(next) = this.watcher_candidate() {
                            match next {
                                Watchers::NextWatch(w1) => (Watcher1, w1, false),
                                Watchers::Satisfied(w1) => (Watcher1, w1, true),
                            }
                        } else {
                            // No vacant slot found. Trying to satisfy watched #2.
                            return Some(match l2.eval() {
                                None => Unit(l2.clone()),
                                Some(true) => Satisfied,
                                Some(false) => Conflict(this.last_definite_watched().clone()),
                            });
                        }
                    }
                    None => {
                        // Undetermined state. Check for Lit #2.
                        match l2.eval() {
                            Some(true) => return Some(Satisfied),
                            Some(false) => {
                                // Unsatisfiable literal in Watched #2: find next available literal for watched2
                                if let Some(next) = this.watcher_candidate() {
                                    match next {
                                        Watchers::NextWatch(w2) => (Watcher2, w2, false),
                                        Watchers::Satisfied(w2) => (Watcher2, w2, true),
                                    }
                                } else {
                                    // No vacant slot found. Lit #1 must be a unit!
                                    return Some(Unit(l1.clone()));
                                }
                            }
                            None => {
                                // No watched literal changed.
                                return None;
                            }
                        }
                    }
                }
            } else {
                // Having only one watched literal.
                // This implies that the clause is a unit clause from its beginning.
                match l1.eval() {
                    Some(false) => return Some(Conflict(l1.clone())),
                    Some(true) => return Some(Satisfied),
                    None => return Some(Unit(l1.clone())),
                }
            }
        };
        self.switch_watcher_to(watcher, new_lit);
        satisfied.then_some(Satisfied)
    }

    // Invariant: lit must be watched literal of self.
    fn propagate(&mut self, lit: &mut CDCLLit) -> Option<ClauseLitState> {
        use ClauseLitState::*;
        {
            let v1 = self.borrow().get_watch1_lit().var();
            let v2 = self.borrow().get_watch2_lit().map(|l| l.var());
            let v = lit.raw_var();
            debug_assert!(
                v1 == v || v2 == Some(v),
                "Propagated literal must be a watched literal: {:?}, watched: {:?}, {:?} ({:?})",
                lit.lit,
                v1,
                v2,
                self.borrow()
            );
        }
        let (watcher, new_lit, satisfied) = {
            let this = self.borrow_mut();
            if this.eval().unwrap_or(false) {
                return Some(Satisfied);
            } else if this.get_watch1().raw_var() == lit.raw_var() {
                if this.get_watch1().eval() == lit.eval() {
                    return Some(Satisfied);
                } else if let Some(next) = this.watcher_candidate() {
                    match next {
                        Watchers::NextWatch(w1) => (Watcher1, w1, false),
                        Watchers::Satisfied(w1) => (Watcher1, w1, true),
                    }
                } else {
                    // No vacant slot found. Check if the clause has more than two literals.
                    match this.get_watch2() {
                        None => {
                            // By clause invariant, the clause has only one literal from the start;
                            // since propagated literal is not satisfied,
                            // this is a contradiction!
                            return Some(Conflict(lit.clone()));
                        }
                        Some(w2) => {
                            match w2.eval() {
                                None => {
                                    // Watched #2 is undetermined. This must be a unit!
                                    return Some(Unit(w2.clone()));
                                }
                                Some(true) => return Some(Satisfied),
                                Some(false) => {
                                    // Both Watched #1 and #2 are false and no slot available.
                                    // Pick the newest variable as the contradiction.
                                    return Some(Conflict(this.last_definite_watched().clone()));
                                }
                            }
                        }
                    }
                }
            } else {
                // By function invariant, propagated unit has the save variable as Watcher #2.
                let w2 = this.get_watch2().unwrap();
                if w2.lit == lit.lit {
                    return Some(Satisfied);
                } else {
                    // Watched #2 is false.
                    // Find next available slot for W2.
                    if let Some(next) = this.watcher_candidate() {
                        match next {
                            Watchers::NextWatch(w2) => (Watcher2, w2, false),
                            Watchers::Satisfied(w2) => (Watcher2, w2, true),
                        }
                    } else {
                        // No slot available!
                        // Check the value of Watched #1.
                        let w1 = this.get_watch1();
                        match w1.eval() {
                            None => {
                                // Watched #1 is undetermined. This must be a unit!
                                return Some(Unit(w1.clone()));
                            }
                            Some(true) => return Some(Satisfied),
                            Some(false) => {
                                // Both Watched #1 and #2 are false and no slot available.
                                // Pick the newest variable as the contradiction.
                                return Some(Conflict(this.last_definite_watched().clone()));
                            }
                        }
                    }
                }
            }
        };
        self.switch_watcher_to(watcher, new_lit);
        satisfied.then_some(Satisfied)
    }
}

type ClauseWeakRef = Weak<RefCell<CDCLClause>>;
type ClauseRef = Rc<RefCell<CDCLClause>>;

type VarRef = Rc<RefCell<CDCLVar>>;

#[derive(Debug)]
enum PropResult {
    NoProp,
    Conflicting(CDCLLit, ClauseRef),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DecisionLevel(usize);

impl Add for DecisionLevel {
    type Output = DecisionLevel;

    fn add(self, rhs: DecisionLevel) -> DecisionLevel {
        DecisionLevel(self.0 + rhs.0)
    }
}

impl Add<u64> for DecisionLevel {
    type Output = DecisionLevel;

    fn add(self, rhs: u64) -> DecisionLevel {
        DecisionLevel(self.0 + rhs as usize)
    }
}

impl AddAssign for DecisionLevel {
    fn add_assign(&mut self, DecisionLevel(rhs): DecisionLevel) {
        self.0 += rhs;
    }
}

impl AddAssign<u64> for DecisionLevel {
    fn add_assign(&mut self, rhs: u64) {
        self.0 += rhs as usize;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Step(u64);

impl Add for Step {
    type Output = Step;

    fn add(self, rhs: Step) -> Step {
        Step(self.0 + rhs.0)
    }
}

impl Add<u64> for Step {
    type Output = Step;

    fn add(self, rhs: u64) -> Step {
        Step(self.0 + rhs)
    }
}

impl AddAssign for Step {
    fn add_assign(&mut self, Step(rhs): Step) {
        self.0 += rhs;
    }
}

impl AddAssign<u64> for Step {
    fn add_assign(&mut self, rhs: u64) {
        self.0 += rhs;
    }
}

#[derive(Debug)]
struct VarValue {
    decision_level: DecisionLevel,
    decision_step: Step,
    reason: Option<ClauseWeakRef>,
    value: bool,
}

#[derive(Debug)]
struct CDCLVar {
    value: Option<VarValue>,
    watched_by: Vec<ClauseWeakRef>,
}

impl CDCLVar {
    fn add_watcher(&mut self, clause: ClauseWeakRef) {
        self.watched_by.push(clause);
    }

    // Removes watching clause from the list, along with staled clauses.
    fn remove_watcher(&mut self, clause: &ClauseRef) {
        self.watched_by
            .retain(|w| w.upgrade().is_some_and(|c| !Rc::ptr_eq(&c, clause)));
    }
}

// TODO: Adaptive Vairable Selection
struct CDCLState {
    vars: HashMap<Var, VarRef>,
    initinal_clauses: Vec<ClauseRef>,
    learnts: Vec<ClauseRef>,
    decision_steps: Vec<Step>,
    history: Option<Vec<Snapshot>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClauseSnapshotLit {
    pub lit: Literal,
    pub state: Option<bool>,
    pub watched: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClauseSnapshot {
    pub lits: Vec<ClauseSnapshotLit>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SnapshotState {
    Propagating {
        unit: Literal,
        reason: Option<ClauseSnapshot>,
        target: Option<ClauseSnapshot>,
        units_detected: Vec<(Literal, Option<ClauseSnapshot>)>,
    },
    Backjumping {
        conflicting: Literal,
        resolution: Vec<Literal>,
    },
    Idle,
}

impl SnapshotState {
    fn propagating(
        unit: &CDCLLit,
        reason: &Option<ClauseRef>,
        target: Option<&ClauseRef>,
        units: &VecDeque<(CDCLLit, Option<ClauseRef>)>,
    ) -> Self {
        SnapshotState::Propagating {
            unit: unit.lit,
            reason: reason.clone().map(|l| l.borrow().snapshot()),
            target: target.map(|l| l.borrow().snapshot()),
            units_detected: units
                .iter()
                .map(|(l, r)| (l.lit, r.as_ref().map(|c| c.borrow().snapshot())))
                .collect(),
        }
    }

    fn backjumping(
        lit: &CDCLLit,
        leftover: &BTreeMap<Step, CDCLLit>,
        learnt: &HashMap<Literal, CDCLLit>,
    ) -> Self {
        SnapshotState::Backjumping {
            conflicting: lit.lit,
            resolution: leftover
                .values()
                .map(|l| l.lit)
                .chain(learnt.keys().cloned())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Snapshot {
    pub decision_level: DecisionLevel,
    pub decision_step: Step,
    pub decisions: Vec<Vec<(Literal, Option<Vec<Literal>>)>>,
    pub clauses: Vec<ClauseSnapshot>,
    pub state: SnapshotState,
}

fn to_assignment(vars: HashMap<Var, VarRef>) -> Assignment {
    vars.into_iter()
        .filter_map(|(v, r)| {
            r.borrow()
                .value
                .as_ref()
                .map(|VarValue { value, .. }| (v, *value))
        })
        .collect()
}

pub fn solve(cnf: &CNF) -> Option<Assignment> {
    CDCLState::new(cnf, false).and_then(|v| v.solve().0)
}

pub fn solve_with_snapshot(cnf: &CNF) -> (Option<Assignment>, Vec<Snapshot>) {
    CDCLState::new(cnf, true).map_or((None, vec![]), |v| {
        let (asgn, snap) = v.solve();
        (asgn, snap.unwrap())
    })
}
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
enum Watcher {
    Watcher1,
    Watcher2,
}
use Watcher::*;

#[derive(Debug, Clone)]
enum BackjumpResult {
    Jumped(CDCLLit, ClauseRef),
    Failed,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Ord, PartialOrd)]
enum AssertLitResult {
    Asserted,
    AlreadySatisfied,
    Contradicting,
}

impl CDCLState {
    fn new(CNF(cnf): &CNF, snapshot: bool) -> Option<CDCLState> {
        let vars = cnf
            .iter()
            .flat_map(|v| v.0.iter())
            .map(Literal::var)
            .unique()
            .map(|v| {
                (
                    v,
                    Rc::new(RefCell::new(CDCLVar {
                        watched_by: Vec::new(),
                        value: None,
                    })),
                )
            })
            .collect::<HashMap<_, _>>();
        let mut dups = false;
        let clauses: Vec<_> = cnf
            .iter()
            .filter_map(|Clause(c)| {
                let lits = {
                    let mut poss = HashSet::new();
                    let mut negs = HashSet::new();
                    c.iter()
                        .filter_map(|a| match a {
                            Pos(v) => {
                                if negs.contains(v) {
                                    dups = true;
                                    None
                                } else {
                                    poss.insert(v);
                                    Some(*a)
                                }
                            }
                            Neg(v) => {
                                if poss.contains(v) {
                                    dups = true;
                                    None
                                } else {
                                    negs.insert(v);
                                    Some(*a)
                                }
                            }
                        })
                        .unique()
                        .map(|l| CDCLLit {
                            lit: l,
                            var: vars.get(&l.var()).unwrap().clone(),
                        })
                        .collect::<Vec<_>>()
                };
                if dups {
                    return None;
                }
                let mut iter = lits.iter().map(|l| l.var.clone()).enumerate();
                let (watching1, watch1) = iter.next()?;
                let (watching2, watch2) = iter.next().map(|(a, b)| (a, b.clone())).unzip();

                let clause = Rc::new(RefCell::new(CDCLClause {
                    lits,
                    watching1,
                    watching2,
                }));

                watch1.borrow_mut().add_watcher(Rc::downgrade(&clause));
                if let Some(w2) = watch2 {
                    w2.borrow_mut().add_watcher(Rc::downgrade(&clause));
                }

                Some(Ok(clause))
            })
            .try_collect::<_, _, ()>()
            .ok()?;
        debug_assert!(
            clauses.iter().all(|c_ref| {
                iter::once(c_ref.borrow().get_watch1())
                    .chain(c_ref.borrow().get_watch2())
                    .all(|w| {
                        w.var
                            .borrow()
                            .watched_by
                            .iter()
                            .any(|d| d.upgrade().is_some_and(|d| Rc::ptr_eq(&d, c_ref)))
                    })
            }),
            "Invalid watching states!"
        );
        let ini0 = CDCLState {
            vars,
            initinal_clauses: clauses,
            learnts: Vec::new(),
            decision_steps: vec![Step(0)],
            history: None,
        };
        let history = snapshot.then_some(vec![ini0.snapshot(SnapshotState::Idle)]);
        Some(CDCLState { history, ..ini0 })
    }

    fn save_snapshot(&mut self, state: SnapshotState) {
        if self.history.is_some() {
            let snapshot = self.snapshot(state);
            self.history.as_mut().unwrap().push(snapshot)
        };
    }

    fn snapshot(&self, state: SnapshotState) -> Snapshot {
        let decision_level = self.current_decision_level();
        let decision_step = *self.decision_steps.last().unwrap();
        let mut decisions = iter::repeat_with(BTreeMap::<Step, _>::new)
            .take(decision_level.0 + 1)
            .collect::<Vec<_>>();
        for (v, r) in &self.vars {
            let r = r.borrow();
            if let Some(val) = &r.value {
                let l = if val.value { Pos(*v) } else { Neg(*v) };
                let reason = val.reason.clone().and_then(|c| {
                    c.upgrade()
                        .map(|c| c.borrow().lits.iter().map(|l| l.lit).collect())
                });
                decisions[val.decision_level.0].insert(val.decision_step, (l, reason));
            }
        }
        let decisions = decisions
            .into_iter()
            .map(|vs| vs.into_values().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let clauses = self
            .get_all_clauses()
            .map(|b| b.borrow().snapshot())
            .collect();
        Snapshot {
            decision_level,
            decision_step,
            decisions,
            clauses,
            state,
        }
    }

    fn solve(mut self) -> (Option<Assignment>, Option<Vec<Snapshot>>) {
        let mut left_over: Option<(CDCLLit, Option<Rc<RefCell<CDCLClause>>>)> = None;
        while !self.is_satisfied() {
            let rule = self.propagate_units(left_over.take());

            match rule {
                PropResult::NoProp => {
                    // No propagation / conflict found.
                    // Decide indefinite variable
                    // TODO: update VSIDS state Here
                    let v = self.vars.iter().find(|&(_, c)| {
                        let c = c.borrow();
                        c.value.is_none()
                    });
                    if let Some((var, cv)) = v {
                        self.decision_steps.push(Step(0));
                        let lit = CDCLLit {
                            lit: Neg(*var),
                            var: cv.clone(),
                        };
                        // self.assert_literal(&mut lit, &None);
                        left_over = Some((lit, None));
                    } else {
                        // No indefinite variable found. Satisfied!
                        break;
                    }
                }
                PropResult::Conflicting(l, p) => {
                    use BackjumpResult::*;
                    if self.current_decision_level() == DecisionLevel(0) {
                        // Conflict at the root level. Unsatisfiable!
                        return (None, self.history);
                    }
                    {}
                    // Conflict found. Learn the clause.
                    match self.backjump(l, p) {
                        Jumped(l, r) => {
                            {}
                            left_over = Some((l, Some(r)));
                        }
                        Failed => {
                            return (None, self.history);
                        }
                    }
                }
            }
        }
        self.save_snapshot(SnapshotState::Idle);
        (Some(to_assignment(self.vars)), self.history)
    }

    fn backjump(&mut self, lit: CDCLLit, reason: ClauseRef) -> BackjumpResult {
        if reason
            .borrow()
            .lits
            .iter()
            .all(|l| Rc::ptr_eq(&l.var, &lit.var))
        {
            return BackjumpResult::Failed;
        }
        let (lit, cls) = self.learn(lit, reason);
        BackjumpResult::Jumped(lit, cls)
    }

    /*
        Learn the 1-UIP clause generated by resolution.

        Resolution of clauses (b, c_1, ..., c_n) and (-b, d_1, ..., d_m) is
        (c_1, ..., c_n, d_1, ..., d_m).

        To reach to 1-UIP, we can do the following:

            1. Let L be the current decision level.
            2. Start with the conflicting literal and clauses.
            3. Pick the last literal in the clause decided in the level L.
            4. If there is only one such literal, it is 1-UIP.
            5. Otherwise, resolve the clause with the literal given by (3) and repeat.

        Carefully analysing the situation, this can be rephrased as follows:

            1. Start with the conflicting literal and clauses.
            2. Add literals decided in level <L to the final 1-UIP.
            3. If there are more than one literals decided in level L, pick the last one and repeat (1).
            4. Otherwise, the only literal decided in level L is 1-UIP.
    */
    fn learn(&mut self, mut lit: CDCLLit, p: ClauseRef) -> (CDCLLit, ClauseRef) {
        let (mut leftover, mut learnt) = self.classify(
            p.borrow()
                .lits
                .iter()
                .filter(|l| l.raw_var() != lit.raw_var())
                .cloned(),
        );
        self.save_snapshot(SnapshotState::backjumping(&lit, &leftover, &learnt));
        debug_assert!(p.borrow().lits.iter().any(|l| l.var.borrow().value.as_ref().map_or(true, |v| v.decision_level == self.current_decision_level())),
            "Conflicting clause {:?} must contain at least one literal decided in this decision level {:?}, but none!",
            &p.borrow().lits.iter().map(|l| (l.clone(), l.var.borrow().value.as_ref().map(|v| v.decision_level))).collect::<Vec<_>>(),
            &self.current_decision_level()
        );
        while !leftover.is_empty() {
            let pair = lit
                .var
                .borrow()
                .value
                .as_ref()
                .and_then(|v| v.reason.as_ref().and_then(|v| v.upgrade()))
                .map(|p| p.borrow().lits.to_vec());

            if let Some(cls) = pair {
                let (lo, older) =
                    self.classify(cls.iter().filter(|l| l.raw_var() != lit.raw_var()).cloned());
                learnt.extend(older);
                leftover.extend(lo.into_iter());
            }
            lit = leftover.pop_last().unwrap().1;
            self.save_snapshot(SnapshotState::backjumping(&lit, &leftover, &learnt));
        }
        lit = if lit.eval() == Some(true) { !lit } else { lit };
        let jump_level = learnt
            .values()
            .filter_map(|l| l.var.borrow().value.as_ref().map(|v| v.decision_level))
            .max()
            .unwrap_or(DecisionLevel(0));
        let watching2 = learnt.iter().next().map(|_| 1);
        let learnt = Rc::new(RefCell::new(CDCLClause {
            lits: iter::once(lit.clone())
                .chain(learnt.into_values())
                .collect(),
            watching1: 0,
            watching2,
        }));

        lit.var.borrow_mut().add_watcher(Rc::downgrade(&learnt));
        self.decision_steps.truncate(jump_level.0 + 1);
        self.learnts.push(learnt.clone());
        for v in self.vars.values() {
            let mut v = v.borrow_mut();
            if let Some(VarValue { decision_level, .. }) = &v.value {
                if *decision_level > jump_level {
                    v.value = None;
                }
            }
        }
        (lit.clone(), learnt)
    }

    fn classify(
        &mut self,
        lits: impl Iterator<Item = CDCLLit>,
    ) -> (BTreeMap<Step, CDCLLit>, HashMap<Literal, CDCLLit>) {
        let level = self.current_decision_level();
        let (lo, older) = lits.partition::<Vec<_>, _>(|l| {
            l.var
                .borrow()
                .value
                .as_ref()
                .map_or(false, |v| v.decision_level == level)
        });
        let lo = lo
            .into_iter()
            .map(|l| {
                (
                    l.var.borrow().value.as_ref().unwrap().decision_step,
                    l.clone(),
                )
            })
            .collect();
        let older = older.into_iter().map(|l| (l.lit, l.clone())).collect();
        (lo, older)
    }

    fn is_satisfied(&self) -> bool {
        // check if satisfied.
        // As the learnt clauses are always consequence of the original clauses,
        // we can check only the original clauses.
        // This saves tremendous amount of time!
        self.initinal_clauses
            .iter()
            .all(|c| c.borrow().eval() == Some(true))
    }

    fn current_decision_level(&self) -> DecisionLevel {
        DecisionLevel(self.decision_steps.len() - 1)
    }

    fn get_all_clauses(&self) -> impl Iterator<Item = &ClauseRef> + '_ {
        self.initinal_clauses.iter().chain(self.learnts.iter())
    }

    fn get_all_clauses_mut(&mut self) -> impl Iterator<Item = ClauseRef> + '_ {
        self.initinal_clauses
            .iter()
            .chain(self.learnts.iter())
            .cloned()
    }

    fn assert_literal(&mut self, l: &mut CDCLLit, c: &Option<ClauseRef>) -> AssertLitResult {
        use AssertLitResult::*;
        match l.eval() {
            None => {
                // TODO: update VSIDS state Here
                let decision_step = *self.decision_steps.last().unwrap();
                let decision_level = self.current_decision_level();
                let reason = c.as_ref().map(Rc::downgrade);
                let value = l.lit.make_true();
                let v = VarValue {
                    decision_level,
                    decision_step,
                    reason,
                    value,
                };
                *self.decision_steps.last_mut().unwrap() += 1;
                l.var.borrow_mut().value.replace(v);
                self.save_snapshot(SnapshotState::Idle);
                Asserted
            }
            Some(true) => AlreadySatisfied,
            Some(false) => Contradicting,
        }
    }

    fn propagate_units(&mut self, unit_reason: Option<(CDCLLit, Option<ClauseRef>)>) -> PropResult {
        use PropResult::*;
        let mut units = unit_reason.into_iter().collect::<VecDeque<_>>();
        // Looping through units, if any.
        loop {
            if let Some((mut l, reason)) = units.pop_front() {
                let state = SnapshotState::propagating(&l, &reason, None, &units);
                self.save_snapshot(state);
                use AssertLitResult::*;
                let resl = self.assert_literal(&mut l, &reason);
                match resl {
                    AlreadySatisfied => continue,
                    Contradicting => {
                        let jump = Conflicting(
                            l.clone(),
                            reason
                                .or_else(|| {
                                    l.var
                                        .borrow_mut()
                                        .value
                                        .as_ref()
                                        .and_then(|v| v.reason.clone())
                                        .and_then(|w| w.upgrade())
                                })
                                .unwrap(),
                        );
                        return jump;
                    }
                    Asserted => {
                        let watcheds = l.var.borrow().watched_by.clone();
                        for c in watcheds {
                            use ClauseLitState::*;
                            // TODO: prune dangling references.
                            if let Some(mut c) = c.upgrade() {
                                self.save_snapshot(SnapshotState::propagating(
                                    &l,
                                    &reason,
                                    Some(&c),
                                    &units,
                                ));
                                let result = c.propagate(&mut l);
                                match result {
                                    None => {
                                        self.save_snapshot(SnapshotState::propagating(
                                            &l,
                                            &reason,
                                            Some(&c),
                                            &units,
                                        ));
                                        continue;
                                    }
                                    Some(Satisfied) => {
                                        self.save_snapshot(SnapshotState::propagating(
                                            &l,
                                            &reason,
                                            Some(&c),
                                            &units,
                                        ));
                                        continue;
                                    }
                                    Some(Conflict(conf_lit)) => {
                                        self.save_snapshot(SnapshotState::propagating(
                                            &l,
                                            &reason,
                                            Some(&c),
                                            &units,
                                        ));
                                        return Conflicting(conf_lit, c);
                                    }
                                    Some(Unit(l2)) => {
                                        units.push_back((l2, Some(c.clone())));
                                        self.save_snapshot(SnapshotState::propagating(
                                            &l,
                                            &reason,
                                            Some(&c),
                                            &units,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                // TODO: traverse unsatisfied clauses only?
                for mut c in self.get_all_clauses_mut() {
                    match c.find_unit() {
                        Some(ClauseLitState::Unit(l)) => {
                            units.push_back((l, Some(c)));
                            continue;
                        }
                        Some(ClauseLitState::Conflict(l)) => {
                            return Conflicting(l, c);
                        }
                        // TODO: flag satisfied clauses?
                        Some(ClauseLitState::Satisfied) => {}
                        None => {}
                    }
                }
                return NoProp;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn test_solve_files() {
        let files = std::fs::read_dir(Path::new("data/uf20-91"))
            .expect("Failed to read directory")
            .map(|f| f.unwrap().path())
            .collect::<Vec<_>>();
        for targ in files {
            let cnf = CNF::parse(&std::fs::read_to_string(&targ).unwrap()).unwrap();
            // for cnf in files {
            //debug_println!("Target: {cnf:?}");
            let answer = solve(&cnf);
            assert!(
                answer.is_some(),
                "{:?} MUST BE satisfiable, but got: {:?}",
                &targ,
                &answer
            );
            if let Some(assign) = answer {
                assert_eq!(
                    cnf.eval(&assign),
                    Some(true),
                    "input: {:?}, bad assignment: {:?}",
                    &cnf,
                    &assign
                );
            }
        }
    }
}

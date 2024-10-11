use std::{
    cell::{Ref, RefCell, RefMut},
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    iter, mem,
    ops::{Add, AddAssign, Mul, MulAssign},
    rc::{Rc, Weak},
};

use itertools::Itertools;

use crate::types::*;

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

impl CDCLLit {
    fn eval(&self) -> Option<bool> {
        self.var
            .borrow()
            .value
            .as_ref()
            .map(|v| self.lit.eval(v.value))
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

    fn get_var(&self, i: usize) -> Ref<CDCLVar> {
        self.lits[i].var.borrow()
    }

    fn get_var_mut<'a>(&'a mut self, i: usize) -> RefMut<CDCLVar> {
        self.lits[i].var.borrow_mut()
    }

    fn get_watcher(&self, w: &Watcher) -> Option<Literal> {
        match w {
            Watcher1 => Some(self.get_watch1_lit()),
            Watcher2 => self.get_watch2_lit(),
        }
    }

    fn get_watch1_lit(&self) -> Literal {
        self.get(self.watching1)
    }

    fn get_watch1(&self) -> &CDCLLit {
        self.lits.get(self.watching1).unwrap()
    }

    fn get_watch1_mut(&mut self) -> &mut CDCLLit {
        self.lits.get_mut(self.watching1).unwrap()
    }

    fn get_watch2_lit(&self) -> Option<Literal> {
        self.watching2.map(|i| self.get(i))
    }

    fn get_watch2(&self) -> Option<&CDCLLit> {
        self.watching2.map(|i| self.lits.get(i).unwrap())
    }

    fn get_watch2_mut(&mut self) -> Option<&mut CDCLLit> {
        self.watching2.map(|i| self.lits.get_mut(i).unwrap())
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
        let mut empty = None;
        for (i, l) in self.lits.iter().enumerate() {
            if l.lit == self.get_watch1_lit() || Some(l.lit) == self.get_watch2_lit() {
                continue;
            }
            match l.eval() {
                None => {
                    empty.get_or_insert(i);
                }
                Some(true) => {
                    return Some(Satisfied(i));
                }
                Some(false) => continue,
            }
        }
        empty.map(Watchers::Satisfied)
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

    fn switch_watcher_to(&mut self, w: Watcher, l: usize);
}

impl ClauseLike for ClauseRef {
    fn switch_watcher_to(&mut self, w: Watcher, l: usize) {
        let watching = match w {
            Watcher1 => &mut self.borrow_mut().watching1,
            Watcher2 => &mut self.borrow_mut().watching2.unwrap(),
        };
        let old = mem::replace(watching, l);
        self.borrow_mut()
            .get_var_mut(old)
            .remove_watcher(Rc::downgrade(self));
        self.borrow_mut()
            .get_var_mut(l)
            .add_watcher(Rc::downgrade(self));
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
}

type ClauseWeakRef = Weak<RefCell<CDCLClause>>;
type ClauseRef = Rc<RefCell<CDCLClause>>;

type VarRef = Rc<RefCell<CDCLVar>>;

#[derive(Debug)]
enum PropResult {
    NoProp,
    Backjump(CDCLLit, ClauseRef),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DecisionLevel(usize);

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Step(u64);

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
    fn remove_watcher(&mut self, clause: ClauseWeakRef) {
        self.watched_by.retain(|w| Weak::ptr_eq(&w, &clause));
    }
}

struct CDCLState {
    vars: HashMap<Var, VarRef>,
    initinal_clauses: Vec<ClauseRef>,
    learnts: Vec<ClauseRef>,
    decision_steps: Vec<Step>,
}

fn to_assignment(vars: HashMap<Var, VarRef>) -> Assignment {
    vars.into_iter()
        .filter_map(|(v, r)| {
            r.borrow()
                .value
                .as_ref()
                .map(|VarValue { value, .. }| (v.clone(), value.clone()))
        })
        .collect()
}

pub fn solve(cnf: &CNF) -> Option<Assignment> {
    CDCLState::new(cnf).and_then(|mut v| v.solve())
}

#[derive(Debug)]
struct Pair<P, V> {
    priority: P,
    value: V,
}

impl<P: PartialEq, V> PartialEq for Pair<P, V> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}
impl<P: Eq, V> Eq for Pair<P, V> {}

impl<P: PartialOrd, V> PartialOrd for Pair<P, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.priority.partial_cmp(&other.priority)
    }
}

impl<P: Ord, V> Ord for Pair<P, V> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.priority.cmp(&other.priority)
    }
}

trait Evalable {
    fn eval_in(&self, state: &CDCLState) -> Option<bool>;
}

impl Evalable for Literal {
    fn eval_in(&self, state: &CDCLState) -> Option<bool> {
        Some(self.eval(self.var().eval_in(state)?))
    }
}

impl Evalable for Var {
    fn eval_in(&self, state: &CDCLState) -> Option<bool> {
        state
            .vars
            .get(self)
            .and_then(|v| v.borrow().value.as_ref().map(|v| v.value))
    }
}

impl Evalable for CDCLClause {
    fn eval_in(&self, state: &CDCLState) -> Option<bool> {
        self.lits
            .iter()
            .map(|l| l.lit.eval_in(state))
            .fold(Some(false), opt_or)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum WatcherCandidate {
    EmptySlots(Vec<usize>),
    Satisfied(usize),
}

impl Add for WatcherCandidate {
    type Output = Self;
    fn add(self: Self, rhs: Self) -> Self {
        use WatcherCandidate::*;
        match (self, rhs) {
            (EmptySlots(ls), EmptySlots(rs)) => EmptySlots(ls.into_iter().chain(rs).collect()),
            (Satisfied(i), _) | (_, Satisfied(i)) => Satisfied(i),
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
enum Watcher {
    Watcher1,
    Watcher2,
}
use Watcher::*;

#[derive(Debug, Clone)]
enum Satisfaction {
    Satisfied,
    Contradiction(Literal, ClauseRef),
    Indeterminate,
}
use Satisfaction::*;

impl Mul for Satisfaction {
    type Output = Satisfaction;
    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Contradiction(l1, c1), _) | (_, Contradiction(l1, c1)) => Contradiction(l1, c1),
            (Indeterminate, _) | (_, Indeterminate) => Indeterminate,
            (Satisfied, Satisfied) => Satisfied,
        }
    }
}

impl MulAssign for Satisfaction {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Ord, PartialOrd)]
enum AssertLitResult {
    Asserted,
    Contradicting,
}

impl CDCLState {
    fn new(CNF(cnf): &CNF) -> Option<CDCLState> {
        println!("Initialising...");
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
        let clauses = cnf
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
                                    Some(a.clone())
                                }
                            }
                            Neg(v) => {
                                if poss.contains(v) {
                                    dups = true;
                                    None
                                } else {
                                    negs.insert(v);
                                    Some(a.clone())
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
        println!("Initialised.");
        Some(CDCLState {
            vars,
            initinal_clauses: clauses,
            learnts: Vec::new(),
            decision_steps: vec![Step(0)],
        })
    }

    fn solve(&mut self) -> Option<Assignment> {
        let mut left_over: Option<(Literal, Option<Rc<RefCell<CDCLClause>>>)> = None;
        println!("Solving: {:?}", self.initinal_clauses);
        while !self.is_satisfied() {
            println!("");
            println!("------------------------------------");
            println!("--- Next ---------------------------");
            println!("------------------------------------");
            println!("");
            let rule = if let Some((l, reason)) = left_over.take() {
                self.propagate(l.clone(), reason)
            } else {
                self.find_unit()
            };
            println!("Rule: {:?}", rule);
            match rule {
                PropResult::Backjump(l, p) => {
                    println!("-------------------------------");
                    println!("Contradiction!: {:?}", (&l, &p));
                    let mut assgn = self
                        .vars
                        .iter()
                        .map(|(Var(v), b)| (v, b.borrow().value.as_ref().map(|v| v.value)))
                        .collect::<Vec<_>>();
                    assgn.sort_by_key(|(v, _)| *v);
                    println!("Contradicting assingments: {:?}", assgn);
                    println!("Contradicting decisions: {:?}", &self.decision_steps);
                    println!("Contradicting clauses: {:?}", &self.initinal_clauses);

                    if self.current_decision_level() > DecisionLevel(0) {
                        println!(
                            "In conflict state. Backjumping... {:?}",
                            &self.decision_steps
                        );
                        left_over = {
                            let (l, c) = self.learn(l, p);
                            Some((l, Some(c)))
                        };
                    } else {
                        println!(
                            "No decision state. Unsatisfiable. {:?}",
                            &self.decision_steps
                        );
                        return None;
                    }
                }
                PropResult::NoProp() => {
                    println!("---------------");
                    println!("No propagation occurred.");
                    // Check if all satisfied or contradicting.
                    match self.check_satisfaction() {
                        Satisfied => {
                            println!("Already satisfied, good!");
                            break;
                        }
                        Contradiction(l, c) => {
                            println!("Contradiction found: {:?}", (&l, &c, l.eval_in(&self)));
                            if self.current_decision_level() > DecisionLevel(0) {
                                println!("In conflict state. Backjumping...");
                                left_over = {
                                    let (l, c) = self.learn(l, c);
                                    Some((l, Some(c)))
                                };
                            } else {
                                println!("No decision state. Unsatisfiable.");
                                return None;
                            }
                        }
                        Indeterminate => {
                            // Otherwise, make a decision.
                            let v = self
                                .vars
                                .iter()
                                .filter_map(|(v, c)| c.borrow().value.is_none().then(|| v))
                                .next();
                            if let Some(v) = v {
                                println!("Making decision: {:?}", &v);
                                self.decision_steps.push(Step(0));
                                left_over = Some((Literal::Pos(v.clone()), None));
                            } else {
                                unreachable!(
                                    "No decision possible. Seems contradicting. coninue..."
                                );
                            }
                        }
                    }
                }
            }
        }
        Some(to_assignment(self.vars.clone()))
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
    fn learn(&mut self, mut lit: Literal, p: ClauseRef) -> (Literal, ClauseRef) {
        let final_level = self.current_decision_level();
        let (mut leftover, mut learnt) = self.classify(
            p.borrow()
                .lits
                .iter()
                .filter(|l| *l.var.borrow() != lit.var())
                .map(|(l, _)| l)
                .cloned(),
        );
        println!("----------");
        println!("Backjumping(init): lit = {:?}, clause = {:?}", &lit, &p);
        debug_assert!(p.borrow().lits.iter().any(|(l, _)| self.vars.get(&l.var()).unwrap().borrow().value.as_ref().map_or(true, |v| v.decision_level == self.current_decision_level())),
            "Conflicting clause {:?} must contain at least one literal decided in this decision level {:?}, but none!",
            &p.borrow().lits.iter().map(|(l, _)| (l.clone(), self.vars.get(&l.var()).unwrap().borrow().value.as_ref().map(|v| v.decision_level.clone()))).collect::<Vec<_>>(),
            &self.current_decision_level()
        );
        println!(
            "Backjumping(init): lit = {:?}, leftover = {:?}, learnt = {:?}",
            &lit, &leftover, &learnt
        );
        while leftover.len() > 0 {
            println!("-----");
            println!(
                "Backjumping(-): lit = {:?}, leftover = {:?}, learnt = {:?}",
                &lit, &leftover, &learnt
            );
            println!(
                "Literal variable reason: {:?}",
                &self
                    .vars
                    .get(&lit.var())
                    .unwrap()
                    .borrow()
                    .value
                    .as_ref()
                    .and_then(|v| v.reason.as_ref().and_then(|v| v.upgrade()))
            );
            let pair = self
                .vars
                .get(&lit.var())
                .unwrap()
                .borrow()
                .value
                .as_ref()
                .and_then(|v| v.reason.as_ref().and_then(|v| v.upgrade()))
                .map(|p| p.borrow().lits.iter().cloned().collect::<Vec<_>>());
            println!("Resolving with {:?}", &pair);

            println!("Pair: {:?}", &pair);
            if let Some(cls) = pair {
                let (lo, older) = self.classify(
                    cls.iter()
                        .filter_map(|(l, _)| (l.var() != lit.var()).then_some(l))
                        .cloned(),
                );
                println!("Incoming leftover = {:?}, learnt = {:?}", &lo, &older);
                learnt.extend(older);
                leftover.extend(lo.into_iter());
            }
            lit = leftover.pop_last().unwrap().value;
        }
        println!("-----");
        lit = match lit.var().eval_in(&self) {
            Some(true) => Neg(lit.var()),
            Some(false) => Pos(lit.var()),
            None => unreachable!(),
        };
        println!(
            "Backjumping(final): lit = {:?}, leftover = {:?}, learnt = {:?}",
            &lit, &leftover, &learnt
        );
        let jump_level = learnt
            .iter()
            .filter_map(|l| {
                self.vars
                    .get(&l.var())
                    .and_then(|v| v.borrow().value.as_ref().map(|v| v.decision_level.clone()))
            })
            .max()
            .unwrap_or(DecisionLevel(0));
        let watching2 = learnt.iter().next().map(|_| 1);
        let learnt = Rc::new(RefCell::new(CDCLClause {
            lits: iter::once(lit)
                .chain(learnt.into_iter())
                .map(|l| (l, self.vars.get(&l.var()).unwrap().clone()))
                .collect(),
            watching1: 0,
            watching2,
        }));

        self.vars
            .get(&lit.var())
            .unwrap()
            .borrow_mut()
            .add_watcher(Rc::downgrade(&learnt));
        self.decision_steps.truncate(jump_level.0 + 1);
        println!("Learned: {:?} with Clause {:?}", lit, &learnt);
        println!(
            "Clause variable levels (curent = {:?}): {:?}",
            &final_level,
            &learnt
                .borrow()
                .lits
                .iter()
                .map(|(l, _)| (
                    l,
                    self.vars[&l.var()]
                        .borrow()
                        .value
                        .as_ref()
                        .map(|v| v.decision_level.clone())
                ))
                .collect::<Vec<_>>()
        );
        self.learnts.push(learnt.clone());
        for v in self.vars.values() {
            let mut v = v.borrow_mut();
            if let Some(VarValue { decision_level, .. }) = &v.value {
                if *decision_level > jump_level {
                    v.value = None;
                }
            }
        }
        println!(
            "Jumped to level: {:?} = {:?}",
            &jump_level, &self.decision_steps
        );
        (lit.clone(), learnt)
    }

    fn classify(
        &mut self,
        lits: impl Iterator<Item = Literal>,
    ) -> (BTreeSet<Pair<Step, Literal>>, HashSet<Literal>) {
        let level = self.current_decision_level();
        let (lo, older) = lits.map(|v| v.clone()).partition::<HashSet<_>, _>(|l| {
            self.vars
                .get(&l.var())
                .unwrap()
                .borrow()
                .value
                .as_ref()
                .map_or(false, |v| v.decision_level == level)
        });
        let lo = lo
            .into_iter()
            .map(|l| Pair {
                priority: self
                    .vars
                    .get(&l.var())
                    .unwrap()
                    .borrow()
                    .value
                    .as_ref()
                    .unwrap()
                    .decision_step
                    .clone(),
                value: l,
            })
            .collect();
        (lo, older)
    }

    fn is_satisfied(&self) -> bool {
        // check if satisfied.
        // As the learnt clauses are always consequence of the original clauses,
        // we can check only the original clauses.
        // This saves tremendous amount of time!
        self.initinal_clauses
            .iter()
            .all(|c| c.borrow().eval_in(self) == Some(true))
    }

    fn check_satisfaction(&self) -> Satisfaction {
        let mut value = Satisfied;
        for c in &self.initinal_clauses {
            let l1 = c.borrow().get_watch1_lit();
            if let Some(l2) = c.borrow().get_watch2_lit() {
                match (l1.eval_in(&self), l2.eval_in(&self)) {
                    (Some(true), _) | (_, Some(true)) => {
                        value *= Satisfied;
                    }
                    _ => {
                        let mut cls_val = Some(false);
                        for (l, _) in &c.borrow().lits {
                            let val = l.eval_in(&self);
                            if let Some(true) = val {
                                cls_val = Some(true);
                                break;
                            } else {
                                cls_val = opt_or(cls_val, val);
                            }
                        }
                        match cls_val {
                            Some(true) => {
                                value *= Satisfied;
                            }
                            Some(false) => {
                                let l = c
                                    .borrow()
                                    .lits
                                    .iter()
                                    .max_by_key(|(_, v)| {
                                        v.borrow()
                                            .value
                                            .as_ref()
                                            .map(|v| (v.decision_level.0, v.decision_step.0))
                                            .unwrap()
                                    })
                                    .unwrap()
                                    .0;
                                return Contradiction(l, c.clone());
                            }
                            None => {
                                value *= Indeterminate;
                            }
                        }
                    }
                }
            } else {
                match l1.eval_in(&self) {
                    Some(true) => {
                        value *= Satisfied;
                    }
                    Some(false) => {
                        return Contradiction(l1, c.clone());
                    }
                    None => {
                        value *= Indeterminate;
                    }
                }
            }
        }
        value
    }

    fn current_decision_level(&self) -> DecisionLevel {
        DecisionLevel(self.decision_steps.len() - 1)
    }

    fn get_all_clauses(&self) -> impl Iterator<Item = Ref<CDCLClause>> {
        self.initinal_clauses
            .iter()
            .chain(self.learnts.iter())
            .map(|c| c.borrow())
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
                let reason = c.as_ref().map(|c| Rc::downgrade(&c));
                let value = l.lit.make_true();
                let v = VarValue {
                    decision_level,
                    decision_step,
                    reason,
                    value,
                };
                *self.decision_steps.last_mut().unwrap() += 1;
                l.var.borrow_mut().value.replace(v);
                return Asserted;
            }
            Some(true) => {
                return Asserted;
            }
            Some(false) => {
                return Contradicting;
            }
        }
    }

    fn propagate_units(&mut self, unit_reason: Option<(CDCLLit, Option<ClauseRef>)>) -> PropResult {
        use PropResult::*;
        let mut units = unit_reason.into_iter().collect::<VecDeque<_>>();
        // Looping through units, if any.
        'outer: loop {
            if let Some((mut l, reason)) = units.pop_front() {
                use AssertLitResult::*;
                let resl = self.assert_literal(&mut l, &reason);
                match resl {
                    Contradicting => {
                        return Backjump(
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
                        )
                    }
                    Asserted => {
                        // TODO: Extract as an external function
                        let mut dest = VecDeque::from([reason]);
                        todo!()
                    }
                }
            } else {
                // TODO: traverse unsatisfied clauses only?
                for mut c in self.get_all_clauses_mut() {
                    match c.find_unit() {
                        Some(ClauseLitState::Unit(l)) => {
                            units.push_back((l, Some(c)));
                            continue 'outer;
                        }
                        Some(ClauseLitState::Conflict(l)) => {
                            return Backjump(l, c);
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

    fn propagate(&mut self, unit: Literal, reason: Option<Rc<RefCell<CDCLClause>>>) -> PropResult {
        use PropResult::*;
        let mut units = VecDeque::from([(unit, reason)]);
        println!("Propagating: {:?}", &unit);
        while let Some((lit, reason)) = units.pop_front() {
            match lit.eval_in(self) {
                Some(true) => {
                    println!("Already assigned, skip: {:?}", &lit);
                    continue;
                }
                Some(false) => {
                    println!("Contradiction found: {:?}", &lit);
                    return Backjump(lit, reason.unwrap());
                }
                None => {}
            }
            println!("Propagating: {:?}", (&lit, &reason));
            let v = lit.var();
            let step = self.decision_steps.last().unwrap().clone();
            let watchers = {
                let mut var_state = self.vars.get(&v).unwrap().borrow_mut();
                assert!(
                    reason.clone().map_or(true, |r| r
                        .borrow()
                        .lits
                        .iter()
                        .map(|(l, _)| l.var())
                        .contains(&lit.var())),
                    "Reason clause doesn't include the unit literal!: {:?} ∉ {:?}",
                    &lit,
                    &reason.map(|r| r.borrow().lits.clone())
                );
                var_state.value = Some(VarValue {
                    decision_level: self.current_decision_level(),
                    decision_step: step,
                    reason: reason.as_ref().map(Rc::downgrade),
                    value: lit.make_true(),
                });
                println!("Var State of {:?}: {:?}", &v, &var_state);
                mem::take(&mut var_state.watched_by)
            };
            *self.decision_steps.last_mut().unwrap() += 1;
            for watcher in watchers {
                if let Some(c_ref) = watcher.upgrade() {
                    println!("\tPropagating {:?} to Watcher: {:?}", &lit, &c_ref);
                    let lit1 = c_ref.borrow().get_watch1_lit();
                    let lit2 = c_ref.borrow().get_watch2_lit();
                    // Detects contradiction or skip if already satisfied.
                    if let Some(lit2) = lit2 {
                        match (lit1.eval_in(self), lit2.eval_in(self)) {
                            (Some(true), _) => {
                                println!("\t\tClause is already satisfied (L1).");
                                continue;
                            }
                            (_, Some(true)) => {
                                println!("\t\tClause is already satisfied (L2).");
                                continue;
                            }
                            (_, _) => {}
                        }
                    } else {
                        // The clause is a unit clause from its beginning.
                        if let Some(is_lit1_true) = lit1.eval_in(self) {
                            if is_lit1_true {
                                println!("\t\tClause is already satisfied (L1).");
                                continue;
                            } else {
                                return Backjump(lit1, c_ref.clone());
                            }
                        }
                    }

                    let frees = self.watcher_candidates(&c_ref.borrow());

                    let (wsing, unit_cand) = if let Some(_) = lit2.filter(|l2| l2.var() == v) {
                        // watched Lit #2 become false.
                        // By invariant (a), we can just seek for new value
                        // only for Lit #2.
                        (Watcher2, Some(lit1))
                    } else {
                        // watched Lit #1 become false.
                        // By invariant (a), we can just seek for new value
                        // only for Lit #1.
                        (Watcher1, lit2)
                    };
                    println!(
                        "\t\tWatcher changed: {:?} = {:?}",
                        wsing,
                        c_ref.borrow().get_watcher(&wsing)
                    );

                    match frees {
                        WatcherCandidate::Satisfied(i) => {
                            println!(
                                "\t\tClause is already satisfied at: {:?} = {:?}",
                                &i,
                                c_ref.borrow().get(i)
                            );
                            self.switch_watcher_to(wsing, &c_ref, i);
                            continue;
                        }
                        WatcherCandidate::EmptySlots(mut frees) => {
                            if let Some(new_watch) = frees.pop() {
                                println!(
                                    "\t\tNew watch found: {:?} = {:?}",
                                    &new_watch,
                                    c_ref.borrow().get(new_watch)
                                );
                                self.switch_watcher_to(wsing, &c_ref, new_watch);
                            } else if let Some(unit_cand) = unit_cand {
                                match unit_cand.eval_in(self) {
                                    None => {
                                        // Unit found!
                                        println!("\t\tPropagating unit: {:?}", &unit_cand);
                                        units.push_back((unit_cand, Some(c_ref.clone())));
                                    }
                                    Some(true) => unreachable!(),
                                    Some(false) => {
                                        println!("\t\tContradiction found: {:?}", &unit_cand);
                                        return Backjump(unit_cand, c_ref.clone());
                                    }
                                }
                            } else {
                                // Conflict
                                println!("\tConflict found!");
                                return Backjump(lit, c_ref.clone());
                            }
                        }
                    }
                }
            }
        }
        return NoProp();
    }

    fn watcher_candidates(&self, c: &CDCLClause) -> WatcherCandidate {
        use WatcherCandidate::*;
        c.lits
            .iter()
            .enumerate()
            .filter_map(|(i, (l, _))| {
                let v = l.var();
                let value = l.eval_in(self);
                match value {
                    Some(true) => Some(Err(Satisfied(i))),
                    Some(false) => None,
                    None => {
                        let not_w1 = v != c.get_watch1_lit().var();
                        let not_w2 = c.get_watch2_lit().map_or(false, |l2| l2.var() != v);
                        if not_w1 && not_w2 {
                            Some(Ok(i))
                        } else {
                            None
                        }
                    }
                }
            })
            .try_collect()
            .map_or_else(|v| v, |f| EmptySlots(f))
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn test_solve_files() {
        println!("Testing...");
        let files = std::fs::read_dir(Path::new("data/uf20-91"))
            .expect("Failed to read directory")
            .map(|f| f.unwrap().path())
            .collect::<Vec<_>>();
        for targ in files {
            println!("Target: {:?}", &targ);
            let cnf = CNF::parse(&std::fs::read_to_string(&targ).unwrap()).unwrap();
            // for cnf in files {
            //println!("Target: {cnf:?}");
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

use crate::types::*;
use itertools::Itertools;
use std::hash::Hash;
use std::{
    cell::{RefCell, RefMut},
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    iter, mem,
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

    fn get_var_mut<'a>(&'a mut self, i: usize) -> RefMut<CDCLVar> {
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
            if l.lit == self.get_watch1_lit() || Some(l.lit) == self.get_watch2_lit() {
                continue;
            }
            match l.eval() {
                None => {
                    new_watcher.get_or_insert(i);
                }
                Some(true) => {
                    return Some(Satisfied(i));
                }
                Some(false) => continue,
            }
        }
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
        println!(
            "Switching watcher: {:?} to {:?} ({:?})",
            &w,
            &l,
            self.borrow()
        );
        let mut this = self.borrow_mut();
        let watching = match w {
            Watcher1 => &mut this.watching1,
            Watcher2 => &mut this.watching2.unwrap(),
        };
        let old = mem::replace(watching, l);
        this.get_var_mut(old).remove_watcher(self);
        this.get_var_mut(l).add_watcher(Rc::downgrade(self));
    }

    fn find_unit(&mut self) -> Option<ClauseLitState> {
        use ClauseLitState::*;
        println!("Finding unit in: {:?}", self);

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
        println!(
            "Switching watcher (sat: {:?}): {:?} to {:?}",
            &satisfied, &watcher, &new_lit
        );
        self.switch_watcher_to(watcher, new_lit);
        satisfied.then_some(Satisfied)
    }

    // Invariant: lit must be watched literal of self.
    fn propagate(&mut self, lit: &mut CDCLLit) -> Option<ClauseLitState> {
        println!("Propagating: {:?} in {:?}", &lit.lit, self);
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
            } else {
                if this.get_watch1().raw_var() == lit.raw_var() {
                    if this.get_watch1().eval() == lit.eval() {
                        return Some(Satisfied);
                    } else {
                        if let Some(next) = this.watcher_candidate() {
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
                                            (Watcher2, this.watching2.unwrap(), false)
                                        }
                                        Some(true) => return Some(Satisfied),
                                        Some(false) => {
                                            // Both Watched #1 and #2 are false and no slot available.
                                            // Pick the newest variable as the contradiction.
                                            return Some(Conflict(
                                                this.last_definite_watched().clone(),
                                            ));
                                        }
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
                            match this.get_watch1().eval() {
                                None => {
                                    // Watched #1 is undetermined. This must be a unit!
                                    (Watcher1, this.watching1, false)
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
        println!("Adding watcher: {:?} to {:?}", &clause.upgrade(), self);
        self.watched_by.push(clause);
    }

    // Removes watching clause from the list, along with staled clauses.
    fn remove_watcher(&mut self, clause: &ClauseRef) {
        println!("Removing watcher: {:?} from {:?}", &clause, self);
        self.watched_by.retain(|w| {
            w.upgrade().is_some_and(|c| {
                if Rc::ptr_eq(&c, clause) {
                    println!("Removing!: {:?}", &c);
                }
                !Rc::ptr_eq(&c, clause)
            })
        });
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
        Some(CDCLState {
            vars,
            initinal_clauses: clauses,
            learnts: Vec::new(),
            decision_steps: vec![Step(0)],
        })
    }

    fn solve(&mut self) -> Option<Assignment> {
        let mut left_over: Option<(CDCLLit, Option<Rc<RefCell<CDCLClause>>>)> = None;
        println!("Solving: {:?}", self.initinal_clauses);
        while !self.is_satisfied() {
            println!("");
            println!("------------------------------------");
            println!("--- Next ---------------------------");
            println!("------------------------------------");
            println!("");
            println!("left_over: {:?}", &left_over);
            let rule = self.propagate_units(left_over.take());

            println!("Rule: {:?}", rule);
            match rule {
                PropResult::NoProp => {
                    println!("---------------");
                    println!("No propagation occurred.");
                    // No propagation / conflict found.
                    // Decide indefinite variable
                    // TODO: update VSIDS state Here
                    let v = self
                        .vars
                        .iter()
                        .filter_map(|(v, c)| c.borrow().value.is_none().then(|| v))
                        .next();
                    if let Some(v) = v {
                        println!("Making decision: {:?}", &v);
                        self.decision_steps.push(Step(0));
                        let mut lit = CDCLLit {
                            lit: Neg(v.clone()),
                            var: self.vars.get(&v).unwrap().clone(),
                        };
                        self.assert_literal(&mut lit, &None);
                        left_over = Some((lit, None));
                    } else {
                        // No indefinite variable found. Satisfied!
                        break;
                    }
                }
                PropResult::Backjump(l, p) => {
                    use BackjumpResult::*;
                    if self.current_decision_level() == DecisionLevel(0) {
                        return None;
                    }
                    // Conflict found. Learn the clause.
                    match self.backjump(l, p) {
                        Jumped(l, r) => {
                            left_over = Some((l, Some(r)));
                        }
                        Failed => return None,
                    }
                }
            }
        }
        Some(to_assignment(self.vars.clone()))
    }

    fn backjump(&mut self, lit: CDCLLit, reason: ClauseRef) -> BackjumpResult {
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
        let final_level = self.current_decision_level();
        let (mut leftover, mut learnt) = self.classify(
            p.borrow()
                .lits
                .iter()
                .filter(|l| l.raw_var() != lit.raw_var())
                .cloned(),
        );
        println!("----------");
        println!("Backjumping(init): lit = {:?}, clause = {:?}", &lit, &p);
        debug_assert!(p.borrow().lits.iter().any(|l| self.vars.get(&l.raw_var()).unwrap().borrow().value.as_ref().map_or(true, |v| v.decision_level == self.current_decision_level())),
            "Conflicting clause {:?} must contain at least one literal decided in this decision level {:?}, but none!",
            &p.borrow().lits.iter().map(|l| (l.clone(), self.vars.get(&l.raw_var()).unwrap().borrow().value.as_ref().map(|v| v.decision_level.clone()))).collect::<Vec<_>>(),
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
                &lit.var
                    .borrow()
                    .value
                    .as_ref()
                    .and_then(|v| v.reason.as_ref().and_then(|v| v.upgrade()))
            );
            let pair = lit
                .var
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
                        .filter_map(|l| (l.raw_var() != lit.raw_var()).then_some(l))
                        .cloned(),
                );
                println!("Incoming leftover = {:?}, learnt = {:?}", &lo, &older);
                learnt.extend(older);
                leftover.extend(lo.into_iter());
            }
            lit = leftover.pop_last().unwrap().value;
        }
        println!("-----");
        lit = !lit;
        println!(
            "Backjumping(final): lit = {:?}, leftover = {:?}, learnt = {:?}",
            &lit, &leftover, &learnt
        );
        let jump_level = learnt
            .iter()
            .filter_map(|l| {
                l.var
                    .borrow()
                    .value
                    .as_ref()
                    .map(|v| v.decision_level.clone())
            })
            .max()
            .unwrap_or(DecisionLevel(0));
        let watching2 = learnt.iter().next().map(|_| 1);
        let learnt = Rc::new(RefCell::new(CDCLClause {
            lits: iter::once(lit.clone()).chain(learnt.into_iter()).collect(),
            watching1: 0,
            watching2,
        }));

        lit.var.borrow_mut().add_watcher(Rc::downgrade(&learnt));
        self.decision_steps.truncate(jump_level.0 + 1);
        println!("Learned: {:?} with Clause {:?}", lit, &learnt);
        println!(
            "Clause variable levels (curent = {:?}): {:?}",
            &final_level,
            &learnt
                .borrow()
                .lits
                .iter()
                .map(|l| l
                    .var
                    .borrow()
                    .value
                    .as_ref()
                    .map(|v| v.decision_level.clone()))
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
        lits: impl Iterator<Item = CDCLLit>,
    ) -> (BTreeSet<Pair<Step, CDCLLit>>, HashSet<CDCLLit>) {
        let level = self.current_decision_level();
        let (lo, older) = lits.map(|v| v.clone()).partition::<HashSet<_>, _>(|l| {
            self.vars
                .get(&l.lit.var())
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
                    .get(&l.lit.var())
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

    fn current_decision_level(&self) -> DecisionLevel {
        DecisionLevel(self.decision_steps.len() - 1)
    }

    fn get_all_clauses_mut(&mut self) -> impl Iterator<Item = ClauseRef> + '_ {
        self.initinal_clauses
            .iter()
            .chain(self.learnts.iter())
            .cloned()
    }

    fn assert_literal(&mut self, l: &mut CDCLLit, c: &Option<ClauseRef>) -> AssertLitResult {
        use AssertLitResult::*;
        println!("Asserting: {:?} ({:?})", &l, &c);
        match l.eval() {
            None => {
                println!("Indeterminate: {:?}; asserting!", &l);
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
                println!("Already satisfied: {:?}", &l);
                return Asserted;
            }
            Some(false) => {
                println!("Assertion failed; contradiction!: {:?}", &l);
                return Contradicting;
            }
        }
    }

    fn propagate_units(&mut self, unit_reason: Option<(CDCLLit, Option<ClauseRef>)>) -> PropResult {
        use PropResult::*;
        let mut units = unit_reason.into_iter().collect::<VecDeque<_>>();
        println!("Propagating units: {:?}", &units);
        // Looping through units, if any.
        'outer: loop {
            if let Some((mut l, reason)) = units.pop_front() {
                use AssertLitResult::*;
                println!("Propagating: {:?}, {:?}", &l, &reason);
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
                        println!("Asserted: {:?}.", &l);
                        let watcheds = l.var.borrow().watched_by.clone();
                        println!(
                            "Propagating {:?} to {:?}",
                            &l,
                            &watcheds.iter().map(|c| c.upgrade()).collect::<Vec<_>>()
                        );
                        for c in watcheds {
                            use ClauseLitState::*;
                            // TODO: prune dangling references.
                            if let Some(mut c) = c.upgrade() {
                                println!("Propagating {:?} to {:?}", &l, &c);
                                match c.propagate(&mut l) {
                                    None => {
                                        println!("Nothing happend");
                                        continue;
                                    }
                                    Some(Satisfied) => {
                                        println!("Satisfied!");
                                        continue;
                                    }
                                    Some(Conflict(conf_lit)) => {
                                        println!("Conflict found: {:?}", &conf_lit);
                                        return Backjump(conf_lit, c);
                                    }
                                    Some(Unit(l)) => {
                                        println!("Unit found: {:?} ({:?})", &l, &c);
                                        units.push_back((l, Some(c)));
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                println!("No units given. searching...");
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
                println!("No more units found. returning...");
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

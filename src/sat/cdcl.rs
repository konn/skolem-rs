use std::{
    cell::RefCell,
    collections::{BinaryHeap, HashMap, HashSet},
    iter, mem,
    ops::{Add, AddAssign, Mul},
    rc::{Rc, Weak},
};

use itertools::Itertools;

use crate::types::*;

use crate::utils::*;
use Literal::*;

#[derive(Debug)]
struct CDCLClause {
    // Invariant (a): at most one of b or -b may occur in literals.
    // Invaliant (b): lits is non-empty.
    lits: Vec<Literal>,
    watching1: usize,
    watching2: Option<usize>,
}

impl CDCLClause {
    fn get(&self, i: usize) -> Literal {
        self.lits[i].clone()
    }

    fn get_watch1(&self) -> Literal {
        self.get(self.watching1)
    }

    fn get_watch2(&self) -> Option<Literal> {
        self.watching2.map(|i| self.get(i))
    }
}

type ClauseWeakRef = Weak<RefCell<CDCLClause>>;
type ClauseRef = Rc<RefCell<CDCLClause>>;

type VarWeakRef = Weak<RefCell<CDCLVar>>;
type VarRef = Rc<RefCell<CDCLVar>>;

#[derive(Debug)]
enum PropagationResult {
    Conflict(Literal, ClauseRef),
    UnitFound(Vec<(Literal, ClauseRef)>),
    NoOp,
}

#[derive(Debug)]
enum Rule {
    NoProp(),
    Backjump(Literal, ClauseRef),
}

impl Mul for PropagationResult {
    type Output = PropagationResult;
    fn mul(self, rhs: PropagationResult) -> PropagationResult {
        match (self, rhs) {
            (NoOp, r) | (r, NoOp) => r,
            (Conflict(i, x), _) | (_, Conflict(i, x)) => Conflict(i, x),
            (UnitFound(mut lits), UnitFound(mut lits2)) => {
                lits.append(&mut lits2);
                UnitFound(lits)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    reason: Option<Weak<RefCell<CDCLClause>>>,
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
}

struct CDCLState {
    vars: HashMap<Var, VarRef>,
    clauses: Vec<ClauseRef>,
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
        self.var().eval_in(state)
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
            .map(|l| l.eval_in(state))
            .fold(None, opt_or)
    }
}

use PropagationResult::*;
impl CDCLState {
    fn new(CNF(cnf): &CNF) -> Option<CDCLState> {
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
                        .collect::<Vec<_>>()
                };
                if dups {
                    return None;
                }
                let mut iter = lits.iter();
                iter.next()?;
                let (watching1, watching2) = { (0, iter.next().map(|_| 1)) };
                let clause = Rc::new(RefCell::new(CDCLClause {
                    lits,
                    watching1,
                    watching2,
                }));

                Some(Ok(clause))
            })
            .try_collect::<_, _, ()>()
            .ok()?;
        Some(CDCLState {
            vars,
            clauses,
            decision_steps: vec![Step(0)],
        })
    }

    fn solve(&mut self) -> Option<Assignment> {
        let mut left_over = None;
        while !self.is_satisfied() {
            let rule = if let Some(l) = left_over {
                self.propagate(vec![l])
            } else {
                self.find_next_step()
            };
            match rule {
                Rule::Backjump(l, p) => {
                    left_over = {
                        let (l, c) = self.learn(l, p);
                        Some((l, Some(c)))
                    }
                }
                Rule::NoProp() => {
                    // Check if all satisfied.
                    if self.is_satisfied() {
                        break;
                    }
                    // Otherwise, make a decision.
                    let v = self
                        .vars
                        .iter()
                        .filter_map(|(v, c)| c.borrow().value.is_none().then(|| v))
                        .next()
                        .unwrap_or_else(|| panic!("No unassigned variable; {:?}", &self.vars));
                    self.decision_steps.push(Step(0));
                    left_over = Some((Literal::Pos(v.clone()), None));
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
        let (mut leftover, mut learnt) = self.classify(p);
        while leftover.len() > 1 {
            let pair = self
                .vars
                .get(&lit.var())
                .unwrap()
                .borrow()
                .value
                .as_ref()
                .and_then(|v| v.reason.as_ref().and_then(|v| v.upgrade()));
            match pair {
                None => break,
                Some(cls) => {
                    let (lo, older) = self.classify(cls);
                    learnt.extend(older);
                    leftover.extend(lo.into_iter());
                    lit = leftover.pop().unwrap().value;
                }
            }
        }
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
            lits: iter::once(lit).chain(learnt.into_iter()).collect(),
            watching1: 0,
            watching2,
        }));
        self.vars
            .get(&lit.var())
            .unwrap()
            .borrow_mut()
            .add_watcher(Rc::downgrade(&learnt));
        self.decision_steps.truncate(jump_level.0);
        (lit.clone(), learnt)
    }

    fn classify(
        &mut self,
        cls: Rc<RefCell<CDCLClause>>,
    ) -> (BinaryHeap<Pair<Step, Literal>>, HashSet<Literal>) {
        let level = self.decision_steps.len();
        let (lo, older) = cls
            .borrow()
            .lits
            .iter()
            .map(|v| v.clone())
            .partition::<HashSet<_>, _>(|l| {
                self.vars
                    .get(&l.var())
                    .unwrap()
                    .borrow()
                    .value
                    .as_ref()
                    .map_or(false, |v| v.decision_level == DecisionLevel(level))
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
        self.clauses
            .iter()
            .all(|c| c.borrow().eval_in(self) == Some(true))
    }

    fn find_next_step(&mut self) -> Rule {
        let result = &self
            .clauses
            .iter()
            .filter_map(|c| {
                let l1 = c.borrow().get_watch1();
                let l2 = c.borrow().get_watch2();
                match l2 {
                    None =>
                    // Unit clause from the beginning
                    {
                        match l1.eval_in(self) {
                            None => Some(UnitFound(vec![(l1, c.clone())])),
                            Some(true) => None,
                            Some(false) => Some(Conflict(l1, c.clone())),
                        }
                    }
                    Some(l2) => match (l1.eval_in(self), l2.eval_in(self)) {
                        (Some(true), _) => None,
                        (_, Some(true)) => None,
                        (None, None) => None,
                        (None, Some(false)) => {
                            let candidates = self.watcher_candidates(&c.borrow());
                            if let Some(w2) = candidates.first() {
                                c.borrow_mut().watching2 = Some(*w2);
                                None
                            } else {
                                Some(UnitFound(vec![(l1, c.clone())]))
                            }
                        }
                        (Some(false), None) => {
                            let candidates = self.watcher_candidates(&c.borrow());
                            if let Some(w2) = candidates.first() {
                                c.borrow_mut().watching2 = Some(*w2);
                                None
                            } else {
                                Some(UnitFound(vec![(l2, c.clone())]))
                            }
                        }
                        (Some(false), Some(false)) => {
                            let candidates = self.watcher_candidates(&c.borrow());
                            let mut iter = candidates.iter();

                            match (iter.next(), iter.next()) {
                                (None, None) => unreachable!(),
                                (Some(w), None) | (None, Some(w)) => {
                                    c.borrow_mut().watching1 = *w;
                                    Some(UnitFound(vec![(c.borrow().get(*w), c.clone())]))
                                }
                                (Some(w1), Some(w2)) => {
                                    c.borrow_mut().watching1 = *w1;
                                    c.borrow_mut().watching2 = Some(*w2);
                                    None
                                }
                            }
                        }
                    },
                }
            })
            .fold(NoOp, PropagationResult::mul);
        match result {
            Conflict(l, c) => Rule::Backjump(*l, c.clone()),
            UnitFound(ls) => {
                self.propagate(ls.into_iter().map(|(l, c)| (*l, Some(c.clone()))).collect())
            }
            NoOp => Rule::NoProp(),
        }
    }

    fn propagate(&mut self, mut units: Vec<(Literal, Option<Rc<RefCell<CDCLClause>>>)>) -> Rule {
        while let Some((lit, reason)) = units.pop() {
            let v = lit.var();
            let step = self.decision_steps.last().unwrap().clone();
            let level = self.decision_steps.len();
            let mut var_state = (*self.vars.get(&v).unwrap()).borrow_mut();
            var_state.value = Some(VarValue {
                decision_level: DecisionLevel(self.decision_steps.len()),
                decision_step: step,
                reason: reason.as_ref().map(Rc::downgrade),
                value: lit.make_true(),
            });
            *self.decision_steps.get_mut(level - 1).unwrap() += 1;
            for watcher in mem::take(&mut var_state.watched_by) {
                if let Some(c_ref) = watcher.upgrade() {
                    let mut c = c_ref.borrow_mut();
                    let lit1 = c.get_watch1();
                    let lit2 = c.get_watch2();
                    // Skip if already satisfied.
                    if lit1.eval_in(self) == Some(true)
                        || lit2.and_then(|l2| l2.eval_in(self)).unwrap_or(true)
                    {
                        continue;
                    }

                    let mut frees = self.watcher_candidates(&c);

                    let (watched, unit_cand) = if lit2.map_or(false, |l2| l2.var() == v) {
                        // watched Lit #2 become false.
                        // By invariant (a), we can just seek for new value
                        // only for Lit #2.
                        (c.watching2.as_mut().unwrap(), Some(lit1))
                    } else {
                        // watched Lit #1 become false.
                        // By invariant (a), we can just seek for new value
                        // only for Lit #1.
                        (&mut c.watching1, lit2)
                    };
                    if let Some(new_watch) = frees.pop() {
                        *watched = new_watch;
                    } else if let Some(unit) = unit_cand {
                        // Unit found!
                        units.push((unit, Some(c_ref.clone())));
                    } else {
                        // Conflict
                        return Rule::Backjump(lit, c_ref.clone());
                    }
                }
            }
        }
        return Rule::NoProp();
    }

    fn watcher_candidates(&self, c: &CDCLClause) -> Vec<usize> {
        c.lits
            .iter()
            .enumerate()
            .filter_map(|(i, l)| {
                let v = l.var();
                let unassigned = self.vars.get(&v).unwrap().borrow().value.is_none();
                let not_w1 = l.var() != c.get_watch1().var();
                let not_w2 = c.get_watch2().map_or(true, |l2| l2.var() != l.var());
                if unassigned && not_w1 && not_w2 {
                    Some(i)
                } else {
                    None
                }
            })
            .collect()
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
        // let files = vec![Path::new("data/uf20-91/uf20-0778.cnf")];
        for targ in files {
            println!("Target: {targ:?}");
            let cnf = CNF::parse(&std::fs::read_to_string(targ).unwrap()).unwrap();
            let answer = solve(&cnf);
            assert!(answer.is_some());
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

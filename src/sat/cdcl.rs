use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    mem,
    ops::{Add, AddAssign},
    rc::{Rc, Weak},
};

use itertools::Itertools;

use crate::types::*;

use Literal::*;

#[derive(Debug)]
struct CDCLClause {
    // Invariant (a): at most one of b or -b occur in literals.
    lits: Vec<Literal>,
    // Invariant (b): if watching1 is None, so is watching2.
    watching1: Option<usize>,
    watching2: Option<usize>,
    satisfied_at: Option<DecisionLevel>,
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
    decision_level: DecisionLevel,
    decision_step: Step,
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
    CDCLState::new(cnf).solve()
}

use PropagationResult::*;
impl CDCLState {
    fn new(CNF(cnf): &CNF) -> CDCLState {
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
                        .collect()
                };
                if dups {
                    return None;
                }
                let (watching1, watching2) = {
                    let mut iter = c.iter();
                    (iter.next().map(|_| 0), iter.next().map(|_| 1))
                };
                let clause = Rc::new(RefCell::new(CDCLClause {
                    lits,
                    watching1,
                    watching2,
                    satisfied_at: None,
                }));

                Some(clause)
            })
            .collect();
        CDCLState {
            vars,
            clauses,
            decision_level: DecisionLevel(0),
            decision_step: Step(0),
        }
    }

    fn solve(self) -> Option<Assignment> {
        while !self.is_satisfied() {
            todo!()
        }
        Some(to_assignment(self.vars))
    }

    fn is_satisfied(&self) -> bool {
        self.clauses
            .iter()
            .all(|c| c.borrow().satisfied_at.is_some())
    }

    fn propagate(
        &mut self,
        lit: &Literal,
        reason: Option<Weak<RefCell<CDCLClause>>>,
    ) -> PropagationResult {
        let v = lit.var();
        let step = self.decision_step.clone();
        let mut var_state = (*self.vars.get(&v).unwrap()).borrow_mut();
        var_state.value = Some(VarValue {
            decision_level: self.decision_level.clone(),
            decision_step: step,
            reason,
            value: lit.make_true(),
        });
        self.decision_step += 1;
        let mut units = Vec::new();

        for watcher in mem::take(&mut var_state.watched_by) {
            if let Some(c_ref) = watcher.upgrade() {
                let mut c = c_ref.borrow_mut();
                let mut frees = c.lits.iter().enumerate().filter_map(|(i, l)| {
                    let v = l.var();
                    let unassigned = self.vars.get(&v).unwrap().borrow().value.is_none();
                    let not_w1 = Some(l.var()) != c.watching1.map(|i| c.lits[i].var());
                    let not_w2 = Some(l.var()) != c.watching2.map(|i| c.lits[i].var());
                    if unassigned && not_w1 && not_w2 {
                        Some(i)
                    } else {
                        None
                    }
                });

                if let Some(l) = c.watching1.map(|i| c.lits[i]).filter(|l| l.var() == v) {
                    if l.eval(lit.make_true()) {
                        c.satisfied_at = Some(self.decision_level.clone());
                        continue;
                    } else {
                        // By invariant (a), watching2 doesn't contain variable v.
                        // So we can safely take watching2 (if present).
                        c_ref.borrow_mut().watching1 = c_ref.borrow_mut().watching2.take();
                    }
                };
                if let Some(_) = c
                    .watching2
                    .map(|i| c.lits[i])
                    .filter(|l| l.var() == v && l.eval(lit.make_true()))
                {
                    c.satisfied_at = Some(self.decision_level.clone());
                    continue;
                } else {
                    c.watching2 = frees.next();
                };
                match (&c.watching1, &c.watching2) {
                    (None, None) => return Conflict(lit.clone(), c_ref.clone()),
                    (Some(_), Some(_)) => (),
                    (Some(i), _) | (_, Some(i)) => units.push((c.lits[*i].clone(), c_ref.clone())),
                }
            }
        }

        if units.is_empty() {
            NoOp
        } else {
            UnitFound(units)
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

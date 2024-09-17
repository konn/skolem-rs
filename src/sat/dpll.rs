use crate::types::*;
use itertools::Itertools;
use std::{collections::HashMap, ops::Add};

type PartialAssignment = HashMap<Var, Option<bool>>;

#[derive(Debug, Clone, PartialEq, Eq)]
struct DpllState {
    clauses: Vec<Clause>,
    assign: PartialAssignment,
    decision_history: Vec<Var>,
}

enum Rule {
    Conflict,
    UnitClause(Literal),
    Decide,
}
use Rule::*;

impl Add for Rule {
    type Output = Rule;
    fn add(self, other: Rule) -> Rule {
        match (self, other) {
            (Conflict, _) | (_, Rule::Conflict) => Rule::Conflict,
            (Decide, r) | (r, Rule::Decide) => r,
            (UnitClause(l), _) => Rule::UnitClause(l),
        }
    }
}

impl DpllState {
    fn new(CNF(cnf): CNF) -> Self {
        let assign = HashMap::from_iter(
            cnf.iter()
                .flat_map(|Clause(c)| c.iter().map(|l| (l.var(), None))),
        );
        let clauses = cnf
            .into_iter()
            .map(|Clause(c)| Clause(c.into_iter().unique().collect()))
            .unique()
            .collect();
        DpllState {
            clauses,
            assign,
            decision_history: vec![],
        }
    }

    fn is_free(&self, v: &Var) -> bool {
        self.assign.get(v).is_none()
    }

    fn next_rule(&self) -> Rule {
        self.clauses
            .iter()
            .map(|Clause(c)| {
                let frees = c
                    .iter()
                    .filter(|&&v| self.is_free(&v.var()))
                    .collect::<Vec<_>>();
                if frees.len() <= 1 {
                    if let Some(&&e) = frees.first() {
                        UnitClause(e)
                    } else {
                        Conflict
                    }
                } else {
                    Decide
                }
            })
            .fold(Rule::Decide, Rule::add)
    }

    fn propagate(&mut self, l: Literal) {
        self.clauses = self
            .clauses
            .iter()
            .filter_map(|Clause(c)| {
                // First removes the negated
                let mut seed = c.into_iter().filter(|&&l2| l2 != -l);
                let sat = seed.by_ref().any(|&l2| l2 == l);
                if sat {
                    None
                } else {
                    Some(Clause(seed.map(|v| *v).collect()))
                }
            })
            .collect();
    }

    fn solve(&mut self) -> Option<Assignment> {
        loop {
            if self.clauses.is_empty() {
                // No clause left. Satisified!
                return Some(
                    self.assign
                        .iter()
                        .filter_map(|(v, b)| b.map(|b| (*v, b)))
                        .collect(),
                );
            }
            // Check if there is any empty or unit clause.
            else {
                match self.next_rule() {
                    UnitClause(l) => {
                        // Unit Clause Found - Make it true!
                        self.assign.insert(l.var(), Some(l.make_true()));
                        self.propagate(l);
                    }
                    Conflict => {
                        // Empty clause reached; unsatisfiable!
                        if let Some(v) = self.decision_history.pop() {
                            // Decision clause; backtrack and assume -v.
                            self.assign.insert(v, Some(false));
                            self.propagate(Literal::Neg(v));
                        } else {
                            return None;
                        }
                    }
                    Decide => {
                        let undec = self.assign.iter().find(|(_, b)| b.is_none()).unzip().0;
                        match undec {
                            None => return None,
                            Some(&v) => {
                                // Applies Decision Rule.
                                self.decision_history.push(v);
                                self.assign.insert(v, Some(true));
                                self.propagate(Literal::Pos(v));
                            }
                        }
                    }
                }
            }
        }
    }
}

pub fn solve(cnf: CNF) -> Option<Assignment> {
    DpllState::new(cnf).solve()
}

use crate::types::*;
use itertools::Itertools;
use std::{collections::HashMap, ops::Mul};

type Level = usize;

type PartialAssignment = HashMap<Var, Option<(bool, Level)>>;

#[derive(Debug, Clone, PartialEq, Eq)]
struct DpllState {
    clauses: Vec<Clause>,
    assign: PartialAssignment,
    decision_history: Vec<Literal>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Status {
    Satisfied,
    Conflict,
    UnitClause(Literal),
    Decide,
}
use Status::*;

impl Mul for Status {
    type Output = Status;
    fn mul(self, other: Status) -> Status {
        match (self, other) {
            (Conflict, _) | (_, Conflict) => Conflict,
            (Satisfied, Satisfied) => Satisfied,
            (Satisfied, r) | (r, Satisfied) => r,
            (Decide, r) | (r, Decide) => r,
            (UnitClause(l), _) => UnitClause(l),
        }
    }
}

impl DpllState {
    fn new(CNF(cnf): &CNF) -> Self {
        let assign = HashMap::from_iter(
            cnf.iter()
                .flat_map(|Clause(c)| c.iter().map(|l| (l.var(), None))),
        );
        let clauses = cnf
            .iter()
            .map(|Clause(c)| Clause(c.iter().unique().copied().collect()))
            .unique()
            .collect();
        DpllState {
            clauses,
            assign,
            decision_history: vec![],
        }
    }

    fn eval(&self, l: &Literal) -> Option<bool> {
        self.assign
            .get(&l.var())
            .and_then(|b| b.map(|(v, _)| l.eval(v)))
    }

    fn get_status(&self) -> Status {
        self.clauses
            .iter()
            .map(|Clause(c)| {
                let mut free = None;
                for l in c {
                    match self.eval(l) {
                        Some(true) => return Satisfied,
                        Some(false) => continue,
                        None => {
                            if free.replace(l).is_some() {
                                return Decide;
                            }
                        }
                    }
                }
                if let Some(l) = free {
                    UnitClause(*l)
                } else {
                    Conflict
                }
            })
            .fold(Satisfied, Status::mul)
    }

    fn propagate(&mut self, l: Literal) {
        self.assign
            .insert(l.var(), Some((l.make_true(), self.decision_history.len())));
    }

    fn clear_decision(&mut self) {
        let lvl = self.decision_history.len();
        for entry in self.assign.values_mut() {
            if let Some((_, l)) = entry {
                if *l > lvl {
                    *entry = None;
                }
            }
        }
    }

    fn solve(&mut self) -> Option<Assignment> {
        'main: loop {
            match self.get_status() {
                Satisfied => {
                    return Some(
                        self.assign
                            .iter()
                            .filter_map(|(v, b)| b.map(|b| (*v, b.0)))
                            .collect(),
                    );
                }
                UnitClause(l) => {
                    // Unit Clause Found - Make it true!
                    self.propagate(l);
                }
                Conflict => {
                    // Empty clause reached; unsatisfiable!
                    while let Some(l) = self.decision_history.pop() {
                        // The first or the second decision failed.
                        match l {
                            Literal::Pos(v) => {
                                // The first decision clause; backtrack and assume -v.
                                self.clear_decision();
                                self.decision_history.push(Literal::Neg(v));
                                self.propagate(Literal::Neg(v));
                                continue 'main;
                            }
                            Literal::Neg(_) => {
                                // Both positive and negative failed.
                                // clear history on the literal and continue to
                                // upper level.
                                self.clear_decision();
                            }
                        }
                    }
                    return None;
                }
                Decide => {
                    let undec = self.assign.iter().find(|(_, b)| b.is_none()).unzip().0;
                    match undec {
                        None => return None,
                        Some(&v) => {
                            // Applies Decision Status.
                            self.decision_history.push(Literal::Pos(v));
                            self.propagate(Literal::Pos(v));
                        }
                    }
                }
            }
        }
    }
}

pub fn solve(cnf: &CNF) -> Option<Assignment> {
    DpllState::new(cnf).solve()
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

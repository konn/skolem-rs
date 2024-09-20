use crate::utils::*;
use std::{collections::HashMap, ops::Neg};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    Pos(Var),
    Neg(Var),
}

impl From<u64> for Var {
    fn from(v: u64) -> Self {
        Var(v)
    }
}

impl From<u64> for Literal {
    fn from(v: u64) -> Self {
        Literal::Pos(Var(v))
    }
}

impl From<i64> for Literal {
    fn from(v: i64) -> Self {
        if v == 0 {
            panic!("0 is not a valid variable");
        } else if v < 0 {
            Literal::Neg(Var((-v) as u64))
        } else {
            Literal::Pos(Var(v as u64))
        }
    }
}

impl Neg for Literal {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Literal::Pos(v) => Literal::Neg(v),
            Literal::Neg(v) => Literal::Pos(v),
        }
    }
}

impl Literal {
    pub fn eval(&self, b: bool) -> bool {
        match self {
            Literal::Pos(_) => b,
            Literal::Neg(_) => !b,
        }
    }

    pub fn var(&self) -> Var {
        match self {
            Literal::Pos(v) => *v,
            Literal::Neg(v) => *v,
        }
    }

    pub fn make_true(&self) -> bool {
        match self {
            Literal::Pos(_) => true,
            Literal::Neg(_) => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause(pub Vec<Literal>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CNF(pub Vec<Clause>);

pub type Assignment = HashMap<Var, bool>;

impl CNF {
    pub fn eval(&self, assign: &Assignment) -> Option<bool> {
        self.0
            .iter()
            .map(|Clause(c)| {
                c.iter()
                    .map(|l| assign.get(&l.var()).map(|&v| l.eval(v)))
                    .fold(Some(false), opt_or)
            })
            .fold(Some(true), opt_and)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    mod cnf {
        use super::*;
        use CNF;

        #[test]
        fn eval() {
            let cnf = CNF(vec![
                Clause(vec![Literal::Pos(Var(1)), Literal::Pos(Var(2))]),
                Clause(vec![Literal::Pos(Var(1)), Literal::Neg(Var(2))]),
            ]);
            let assign = [(Var(1), true)].into_iter().collect();
            assert_eq!(cnf.eval(&assign), Some(true));
            let assign = [(Var(1), false), (Var(2), false)].into_iter().collect();
            assert_eq!(cnf.eval(&assign), Some(false));
        }
    }
}

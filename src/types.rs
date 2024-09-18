use std::{collections::HashMap, ops::Neg};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u64);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    Pos(Var),
    Neg(Var),
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

fn opt_or(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), r) | (r, Some(false)) => r,
        (None, None) => None,
    }
}

fn opt_and(l: Option<bool>, r: Option<bool>) -> Option<bool> {
    match (l, r) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), r) | (r, Some(true)) => r,
        (None, None) => None,
    }
}

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

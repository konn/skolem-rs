use std::{collections::HashMap, ops::Neg};

pub type Var = u64;

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

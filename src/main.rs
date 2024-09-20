use skolem::sat::cdcl;
use skolem::types;
use skolem::types::{Clause, Literal, Var, CNF};

pub fn main() {
    let cnf = CNF(vec![
        vec![-1, -2, -3, -4, 5],
        vec![-3, -4, -6],
        vec![-5, 6, -1, 7],
        vec![-7, 8],
        vec![-2, -7, 9],
        vec![-8, -9, 10],
    ]
    .iter()
    .map(|c| Clause(c.iter().cloned().map(|i: i64| Literal::from(i)).collect()))
    .collect());
    cdcl::solve(&cnf);
}

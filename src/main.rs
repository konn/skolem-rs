use skolem::sat::cdcl;
use skolem::types::*;

pub fn main() {
    /* let cnf = CNF([
        vec![-1, -2, -3, -4, 5],
        vec![-3, -4, -6],
        vec![-5, 6, -1, 7],
        vec![-7, 8],
        vec![-2, -7, 9],
        vec![-8, -9, 10],
        vec![-10, 11],
        vec![-11, 12],
        vec![-10, -2, -12],
    ]
    .iter()
    .map(|c| Clause(c.iter().cloned().map(|i: i64| Literal::from(i)).collect()))
    .collect()); */
    let cnf = CNF::parse(&std::fs::read_to_string("data/uf20-91/uf20-0778.cnf").unwrap()).unwrap();
    cdcl::solve(&cnf);
}

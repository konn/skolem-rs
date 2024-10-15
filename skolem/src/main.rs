use anyhow::{anyhow, bail, ensure, Result};
use skolem::sat::cdcl;
use skolem::{clause, types::*};
use std::fs;
use std::path::Path;

pub fn main() -> Result<()> {
    /* let cnf = CNF(vec![
        clause![-1 -2 -3 -4 5],
        clause![-3 - 4 - 6],
        clause![-5 6 -1 7],
        clause![-7 8],
        clause![-2 -7 9],
        clause![-8 -9 10],
        clause![-10 11],
        clause![-11 12],
        clause![-10 - 2 - 12],
    ]); */

    // let cnf = CNF::parse(&std::fs::read_to_string("data/uf20-91/uf20-0778.cnf").unwrap()).unwrap();
    // let cnf = CNF(clauses.into_iter().take(80).collect());
    let cnf = CNF(vec![
        clause![-1, -18, -19],
        clause![-1, 7, -6],
        clause![-12, -1, 5],
        clause![-12, 4, 6],
        clause![-13, -16, -7],
        clause![-14, -15, -13],
        clause![-15, 10, 6],
        clause![-15, 6, 14],
        clause![-17, -11, -2],
        clause![-17, 10, 20],
        clause![-17, 19, -8],
        clause![-18, -7, -3],
        clause![-19, -3, -8],
        clause![-19, -5, 10],
        clause![-19, 1, -13],
        clause![-19, 17, 12],
        clause![-19, 20, -9],
        clause![-19, 7, 14],
        clause![-20, -8, 10],
        clause![-4, -2, 18],
        clause![-4, 2, 20],
        clause![-5, -9, -8],
        clause![-5, 20, 11],
        clause![-5, 9, -7],
        clause![-6, -20, -18],
        clause![-6, 10, 14],
        clause![-7, -13, -12],
        clause![-7, -18, 13],
        clause![-7, 10, 16],
        clause![-7, 17, 2],
        clause![-9, -8, -13],
        clause![1, -17, 5],
        clause![1, -18, -10],
        clause![1, 9, 5],
        clause![10, -14, -2],
        clause![10, 8, 11],
        clause![11, -2, 19],
        clause![11, 7, 17],
        clause![12, 6, -17],
        clause![13, 18, 16],
        clause![14, -7, 19],
        clause![15, -18, 6],
        clause![15, 7, 18],
        clause![16, 6, -11],
        clause![17, -10, 8],
        clause![17, 1, -15],
        clause![17, 18, -8],
        clause![17, 8, 11],
        clause![18, -9, 4],
        clause![19, 16, -8],
        clause![2, -19, 1],
        clause![2, -6, 13],
        clause![2, -9, 14],
        clause![20, -8, -6],
        clause![20, 2, 4],
        clause![4, 8, -12],
        clause![4, 9, -6],
        clause![5, -3, -14],
        clause![5, 7, 15],
        clause![6, -17, -20],
        clause![6, -18, 16],
        clause![6, -7, 15],
        clause![8, -9, 6],
        clause![8, 12, -20],
        clause![8, 18, 19],
        clause![8, 3, 11],
        clause![9, -4, 10],
    ]);
    println!("Solving: {:?}", cnf);
    println!();
    println!("------------------------");
    println!();
    let (assign, snap) = cdcl::solve_with_snapshot(&cnf);
    println!("{:?}", snap.len());
    let path = Path::new("workspace/sat.json");
    fs::create_dir_all(path.parent().ok_or(anyhow!("Unwrap"))?)?;
    fs::write(path, serde_json::to_string(&snap)?)?;
    match assign {
        Some(assign) => {
            ensure!(
                cnf.eval(&assign) == Some(true),
                "MustBe true, but got: {:?}",
                assign
            )
        }
        None => bail!("UNSAT"),
    }
    Ok(())
}

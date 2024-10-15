use std::num::ParseIntError;

use itertools::Itertools;

use crate::types::*;

impl Literal {
    pub fn parse(source: &str) -> Result<Self, String> {
        let mut source = source.chars().skip_while(|c| c.is_whitespace()).peekable();
        let cons = match source.peek() {
            Some('-') => {
                source.next();
                Literal::Neg
            }
            _ => Literal::Pos,
        };
        let var: Var = source
            .collect::<String>()
            .parse()
            .map(Var)
            .map_err(|e: ParseIntError| format!("Invalid variable: {e}"))?;
        Ok(cons(var))
    }
}

use itertools::EitherOrBoth::*;
impl CNF {
    pub fn parse(source: &str) -> Result<Self, String> {
        let mut lines = source.lines().skip_while(|l| l.starts_with("c"));
        let problem_line0 = lines.next().ok_or("No problem line")?;
        let mut problem_line = problem_line0.split_whitespace();
        problem_line.next().ok_or(format!(
            "No problem line header: empty! (header: {:?})",
            problem_line
        ))?;
        problem_line.next().ok_or(format!(
            "No problem line header: empty! (header: {:?})",
            problem_line
        ))?;
        let _num_vars: u64 = problem_line
            .next()
            .ok_or("# of variables expected, but missing!")?
            .parse()
            .map_err(|e| format!("Invalid # of vars: {e:} (input: {:?})", problem_line0))?;
        let num_clauses: u64 = problem_line
            .next()
            .ok_or("# of clauses expected, but missing!")?
            .parse()
            .map_err(|e| format!("Invalid # of clauses: {e:}"))?;
        let clauses = lines
            .flat_map(str::split_ascii_whitespace)
            .map(str::to_string)
            .filter(|s| !s.is_empty())
            .collect::<Vec<_>>()
            .split(|s| s == "0")
            .zip_longest(0..num_clauses)
            .flat_map(|em| match em {
                Both(c, _) => Some(
                    c.iter()
                        .map(|s| Literal::parse(s))
                        .try_collect()
                        .map(Clause),
                ),
                Right(i) => Some(Err(format!(
                    "Expected {num_clauses:?} clauses, but got {i:?}"
                ))),
                Left(_) => None,
            })
            .try_collect()?;
        Ok(CNF(clauses))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use Var;

    mod literal {
        use super::*;
        use Literal::*;

        #[test]
        fn test_parse() {
            let cases = [("12", Pos(Var(12))), ("-13", Neg(Var(13)))];
            for (source, expected) in cases.iter() {
                assert_eq!(Literal::parse(source), Ok(*expected), "Input: {:?}", source);
            }
        }
    }

    mod cnf {
        use std::path::Path;

        use super::*;
        use Clause;
        use Literal::*;
        use CNF;

        #[test]
        fn test_parse() {
            let cases = [
                ("p cnf 1 1\n1", Ok(vec![vec![Pos(Var(1))]])),
                ("p cnf 1 1\n1 0 124", Ok(vec![vec![Pos(Var(1))]])),
                ("p cnf 3 4\n1 0 124", Err("Expected 4 clauses, but got 2")),
                (
                    "p cnf 3 3\n1 0 3 -2\n1 0 1",
                    Ok(vec![
                        vec![Pos(Var(1))],
                        vec![Pos(Var(3)), Neg(Var(2)), Pos(Var(1))],
                        vec![Pos(Var(1))],
                    ]),
                ),
            ];
            for (source, expected) in cases {
                assert_eq!(
                    CNF::parse(source),
                    expected
                        .map_err(str::to_string)
                        .map(|x| CNF(x.iter().map(|v| Clause(v.clone())).collect::<Vec<_>>())),
                    "Input: {:?}",
                    source
                );
            }
        }

        #[test]
        fn test_parse_files() {
            // List files under "data/uf20-91"
            let files = std::fs::read_dir(Path::new("data/uf20-91"))
                .expect("Failed to read directory")
                .map(|f| f.unwrap().path());
            for file in files {
                println!("Parsing: {:?}", file);
                let source = std::fs::read_to_string(&file).expect("Failed to read file");
                assert!(CNF::parse(&source).is_ok())
            }
        }
    }
}

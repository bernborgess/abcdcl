use dimacs::*;
use std::env;
use std::fs;

// TODO: Return the datastructure we want to work with
pub fn read_cnf() -> (Vec<Vec<i64>>, usize) {
    let args: Vec<String> = env::args().collect();
    let dimacs_filename = args[1].as_str();
    let contents = fs::read_to_string(dimacs_filename).expect("Couldn't find the DIMACS file ");

    let (num_vars, clauses) = match parse_dimacs(&contents).unwrap() {
        Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
        Instance::Sat { .. } => panic!("Received (valid) SAT input, not CNF"),
    };
    eprintln!(
        "Working with {num_vars} variables and {} clauses.",
        clauses.len()
    );
    let mut cnf_vec: Vec<Vec<i64>> = vec![];
    for clause in clauses.iter() {
        let mut clause_vec = Vec::new();
        for l in clause.lits().iter() {
            let b = match l.sign() {
                Sign::Neg => false,
                Sign::Pos => true,
            };
            eprint!("{}{} ", if b { "+" } else { "-" }, l.var().to_u64());
            let val: i64 = l.var().to_u64() as i64;
            // add this lit to the clause at the right idx
            clause_vec.push(if b { val } else { -val });
        }
        eprintln!();
        cnf_vec.push(clause_vec);
    }
    (cnf_vec, num_vars.try_into().unwrap())
}

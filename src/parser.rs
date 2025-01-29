use dimacs::*;
use std::env;
use std::fs;

pub fn read_from_string(dimacs_filename: &str) -> (Vec<Vec<i64>>, usize) {
    let contents = fs::read_to_string(dimacs_filename).expect("Couldn't find the DIMACS file ");
    let (num_vars, clauses) = match parse_dimacs(&contents).unwrap() {
        Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
        Instance::Sat { .. } => panic!("Received (valid) SAT input, not CNF"),
    };
    let mut cnf_vec: Vec<Vec<i64>> = vec![];
    for clause in clauses.iter() {
        let mut clause_vec = Vec::new();
        for l in clause.lits().iter() {
            let b = match l.sign() {
                Sign::Neg => false,
                Sign::Pos => true,
            };
            let val: i64 = l.var().to_u64() as i64;
            clause_vec.push(if b { val } else { -val });
        }
        cnf_vec.push(clause_vec);
    }
    (cnf_vec, num_vars.try_into().unwrap())
}

pub fn read_cnf() -> (Vec<Vec<i64>>, usize) {
    let args: Vec<String> = env::args().collect();
    let dimacs_filename = args[1].as_str();
    let contents = fs::read_to_string(dimacs_filename).expect("Couldn't find the DIMACS file ");

    let (num_vars, clauses) = match parse_dimacs(&contents).unwrap() {
        Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
        Instance::Sat { .. } => panic!("Received (valid) SAT input, not CNF"),
    };
    let mut cnf_vec: Vec<Vec<i64>> = vec![];
    for clause in clauses.iter() {
        let mut clause_vec = Vec::new();
        for l in clause.lits().iter() {
            let b = match l.sign() {
                Sign::Neg => false,
                Sign::Pos => true,
            };
            let val: i64 = l.var().to_u64() as i64;
            clause_vec.push(if b { val } else { -val });
        }
        cnf_vec.push(clause_vec);
    }
    (cnf_vec, num_vars.try_into().unwrap())
}

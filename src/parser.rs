use dimacs::*;
use std::env;
use std::fs;

// TODO: Return the datastructure we want to work with
pub fn read_cnf() {
    let args: Vec<String> = env::args().collect();
    let dimacs_filename = args[1].as_str();
    let contents = fs::read_to_string(dimacs_filename).expect("Couldn't find the DIMACS file ");

    let (num_vars, clauses) = match parse_dimacs(&contents).unwrap() {
        Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
        Instance::Sat { .. } => panic!("Received (valid) SAT input, not CNF"),
    };
    println!(
        "Working with {num_vars} variables and {} clauses.",
        clauses.len()
    );
    for clause in clauses.iter() {
        for l in clause.lits().iter() {
            let b = match l.sign() {
                Sign::Neg => false,
                Sign::Pos => true,
            };
            print!("{}{} ", if b { "+" } else { "-" }, l.var().to_u64());
        }
        // comment
        println!();
    }
}

use dimacs::*;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    let dimacs_filename = args[1].as_str();
    let contents = fs::read_to_string(dimacs_filename).expect("Couldn't find the DIMACS file ");

    let (_, cvec) = match parse_dimacs(&contents).unwrap() {
        Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
        Instance::Sat {
            num_vars: _,
            extensions: _,
            formula: _,
        } => panic!("Received (valid) SAT input, not CNF"),
    };
    for itm in cvec.iter() {
        for l in itm.lits().iter() {
            let b = match l.sign() {
                Sign::Neg => false,
                Sign::Pos => true,
            };
            println!("{}{:?}", if b { "+" } else { "-" }, l);
        }
        println!();
    }
}

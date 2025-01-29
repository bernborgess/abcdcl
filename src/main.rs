use abcdcl::{
    cdcl::{run_cdcl, CdclResult},
    parser::read_cnf,
};

fn main() {
    let (cnf, lits) = read_cnf();
    let result = run_cdcl(&cnf, lits);
    match result {
        CdclResult::SAT(model) => {
            println!("SAT");
            for (i, b) in model.iter().enumerate() {
                if *b {
                    print!("{i} ");
                } else {
                    print!("-{i} ");
                }
            }
            println!();
        }
        CdclResult::UNSAT => println!("\nUNSAT"),
    }
}

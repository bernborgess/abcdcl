use abcdclt::{
    cdcl::{run_cdcl, CdclResult},
    parser::read_cnf,
};

fn main() {
    let (cnf, lits) = read_cnf();
    // TODO: Pass the right number of literals!
    let result = run_cdcl(cnf, lits);
    match result {
        CdclResult::SAT(_) => println!("\nSAT"),
        CdclResult::UNSAT => println!("\nUNSAT"),
        CdclResult::Mock(_) => println!("What"),
    }
    // eprintln!("{:?}", result);
    //run_demo()
}

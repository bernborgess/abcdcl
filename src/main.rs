use abcdcl::{
    cdcl::{run_cdcl, CdclResult},
    parser::read_cnf,
};
// TODO:
// The output should be the SAT competition variation of the format.
// Specifically, it should be a sequence of two lines. The first line should be
// `s SATISFIABLE` or `s UNSATISFIABLE`. The next line should be blank unless the
// first line is s SATISFIABLE. In that case, it should be v M , where M is a
// space-separated list of non-contradictory literals, where each literal is just
// a positive or negative (non-zero) integer.
fn main() {
    let (cnf, lits) = read_cnf();
    let result = run_cdcl(&cnf, lits);
    match result {
        CdclResult::SAT(model) => {
            println!("SAT");
            for (i, b) in model.iter().enumerate() {
                if *b {
                    print!("{} ", i + 1);
                } else {
                    print!("-{} ", i + 1);
                }
            }
            println!("0");
        }
        CdclResult::UNSAT => println!("\nUNSAT"),
    }
}

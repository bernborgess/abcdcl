use abcdclt::{cdcl::run_cdcl, parser::read_cnf};

fn main() {
    let cnf = read_cnf();
    // TODO: Pass the right number of literals!
    let result = run_cdcl(cnf, 3);
    println!("{:?}", result);
}

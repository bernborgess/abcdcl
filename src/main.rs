use abcdclt::{cdcl::run_cdcl, parser::read_cnf};

fn main() {
    let cnf = read_cnf();
    let result = run_cdcl(cnf);
    println!("{:?}", result);
}

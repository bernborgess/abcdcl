use abcdclt::{cdcl::run_cdcl, parser::read_cnf};

fn main() {
    let cnf = read_cnf();
    run_cdcl(cnf);
}

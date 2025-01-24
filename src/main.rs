use abcdclt::{
    cdcl::{run_cdcl, run_demo},
    parser::read_cnf,
};

fn main() {
    let (cnf, lits) = read_cnf();
    // TODO: Pass the right number of literals!
    let result = run_cdcl(cnf, lits);
    match result {
        CdclResult::SAT(_) => println!("SAT"),
        CdclResult::UNSAT => println!("UNSAT"),
    }
    // eprintln!("{:?}", result);
    //run_demo()
}

use abcdclt::cdcl::*;

fn main2() {
    let mut solver: Cdcl = Cdcl::new(7);
    let original_cnf: Vec<Vec<i64>> = vec![
        //must remove clauses with 1 (verified by unit clause) or -2 (verified by pure)
        vec![-1, -2],
        vec![1],
        vec![-2, 3, 4, 5],
        vec![6, -7],
        vec![5, 7],
        vec![1, -5, 6],
        vec![1, -2, 5],
        vec![-1, 4, 5],
        vec![-3, -4, -6],
        vec![1, -4],
        vec![-3, 4, -5],
    ];
    let target_cnf: Vec<Vec<i64>> = vec![
        //must remove clauses with 1 (verified by unit clause) or -2 (verified by pure)
        vec![6, -7],
        vec![5, 7],
        vec![-1, 4, 5],
        vec![-3, -4, -6],
        vec![-3, 4, -5],
    ];
    solver.pre_process(original_cnf);
    eprintln!("target");
    eprintln!("{:?}", &target_cnf);
    eprintln!("encontrado");
    eprintln!("{:?}", &solver.clauses_list);
    /*for (i, c) in solver.clauses_list.iter().enumerate(){
        for (j,&lit) in c.data.iter().enumerate(){
            assert_eq!(lit,target_cnf[i][j]);
        }
    }*/
}

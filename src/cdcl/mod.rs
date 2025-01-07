#[derive(Debug)]
pub enum Assignment {
    U,
    T,
    F,
}

#[derive(Debug)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<Assignment>),
}

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>) -> CdclResult {
    println!("TODO: cdcl run {:?}", cnf);
    // while(true){
    //     while (propagate_gives_conflict()){
    //         if (decision_level==0) return UNSAT;
    //         else analyze_conflict();
    //     }
    //     restart_if_applicable();
    //     remove_lemmas_if_applicable();
    //     if (!decide()) returns SAT; // All vars assigned
    // }
    CdclResult::UNSAT
}

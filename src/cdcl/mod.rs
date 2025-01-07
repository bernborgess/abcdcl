#[derive(Debug, PartialEq)]
pub enum Assignment {
    U,
    T,
    F,
}

#[derive(Debug, PartialEq)]
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

#[cfg(test)]
mod tests {
    use super::*;
    use CdclResult::*;

    #[test]
    fn empty_cnf_is_unsat() {
        let result = run_cdcl(vec![]);
        assert_eq!(result, UNSAT);
    }

    #[test]
    fn single_cnf_is_sat() {
        let result = run_cdcl(vec![vec![1]]);
        match result {
            UNSAT => panic!("Expected SAT"),
            SAT(assign) => {
                println!("Oh cool. {:?}", assign);
            }
        }
    }
}

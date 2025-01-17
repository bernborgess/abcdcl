#[derive(Debug, PartialEq)]
pub enum Assignment {
    U,
    T,
    F,
}

#[derive(Clone, Debug)]
enum Seen {
    Unseen,
    SeenPositive,
    SeenNegative,
    SeenBoth,
}

#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<Assignment>),
}

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    println!("TODO: cdcl run {:?}", cnf);
    let mut solver = Cdcl::new(cnf, lits);
    solver.pure();
    // while(true){
    //     while (propagate_gives_conflict()){
    //         if (decision_level==0) return UNSAT;
    //         else analyze_conflict();
    //     }
    //     restart_if_applicable();
    //     remove_lemmas_if_applicable();
    //     if (!decide()) returns SAT(self.format()); // All vars assigned
    // }
    CdclResult::UNSAT
}

struct InnerAssignment{
    literal: usize,
    asgn: Assignment,
    decision_level: usize,
}

struct Cdcl {
    partial_model: Vec<InnerAssignment>,
    clauses: Vec<Vec<i64>>,
    confliting_literals: Vec<usize>,
    number_of_lits: usize,
    decision_level: usize,
    confliting: Option<Vec<i64>>,
}

impl Cdcl {
    fn new(cnf: Vec<Vec<i64>>, lits: usize) -> Cdcl {
        let n = cnf.len();
        Cdcl {
            partial_model: vec![],
            clauses: cnf,
            confliting_literals: vec![0;n],
            number_of_lits: lits,
            decision_level: 0,
            confliting: None,
        }
    }

    fn pure(&mut self) -> () {
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_lits]; 
        for clause in self.clauses.iter(){
            for lit in clause.iter(){
                if *lit<0{
                    let index = (-lit-1) as usize;
                    seen_status[index] = match seen_status[index] {
                        Seen::Unseen => Seen::SeenNegative,
                        Seen::SeenPositive => Seen::SeenBoth,
                        Seen::SeenNegative => Seen::SeenNegative,
                        Seen::SeenBoth => Seen::SeenBoth,
                    };
                } else if *lit > 0 {
                    let index = (lit - 1) as usize;
                    seen_status[index] = match seen_status[index] {
                        Seen::Unseen => Seen::SeenPositive,
                        Seen::SeenPositive => Seen::SeenPositive,
                        Seen::SeenNegative => Seen::SeenBoth,
                        Seen::SeenBoth => Seen::SeenBoth,
                    };
                } else {
                    panic!("0 in clause!!!!\nThis is not a valid CNF");
                }
            }
        }
        for (index, status) in seen_status.iter().enumerate() {
            match status {
                Seen::Unseen => (),
                Seen::SeenPositive => self.partial_model.push(
                    InnerAssignment{
                        literal: index, 
                        asgn: Assignment::T, 
                        decision_level: 0
                    }
                ),
                Seen::SeenNegative => self.partial_model.push(    
                    InnerAssignment{
                        literal: index,
                        asgn: Assignment::F, 
                        decision_level: 0
                    }
                ),
                Seen::SeenBoth => (),
            }
        }
    }

    fn propagate_gives_conflict(&mut self) -> bool {
        self.propagate(1);
        return self.confliting != None
    }

    fn propagate(&mut self, lit: i64){
        let asgn;
        if lit<0{
            asgn = InnerAssignment{
                literal: -lit as usize, 
                asgn: Assignment::F, 
                decision_level: self.decision_level
            }
        } else {
            asgn = InnerAssignment{
                literal: lit as usize, 
                asgn: Assignment::T, 
                decision_level: self.decision_level
            }
        }

        self.partial_model.push(asgn);
    }

    fn format(&self) -> Vec<Assignment> {
        println!("TODO: format");
        vec![]
    }

    fn analyze_conflict(&self) {
        println!("TODO: analyze_conflict");
    }

    fn restart_if_applicable(&self) {
        println!("TODO: restart_if_applicable");
    }

    fn remove_lemmas_if_applicable(&self) {
        println!("TODO: remove_lemmas_if_applicable");
    }

    fn decide(&self) -> bool {
        println!("TODO: decide");
        false
    }

    
}
#[cfg(test)]
mod tests {
    use super::*;
    use Assignment::*;
    use CdclResult::*;

    #[test]
    fn empty_cnf_is_unsat() {
        let result = run_cdcl(vec![], 0);
        assert_eq!(result, UNSAT);
    }

    #[test]
    fn single_cnf_is_sat() {
        let result = run_cdcl(vec![vec![1]], 1);
        match result {
            UNSAT => panic!("Expected SAT"),
            SAT(assign) => {
                assert_eq!(assign.len(), 1);
                assert_eq!(assign[0], T);
            }
        }
    }

    #[test]
    fn two_cnf_is_sat() {
        let result = run_cdcl(vec![vec![1, 2], vec![-1, -2]], 2);
        match result {
            UNSAT => panic!("Expected SAT"),
            SAT(assign) => {
                assert_eq!(assign.len(), 2);
                // Either [T,F] or [F,T]
                assert!(assign == vec![T, F] || assign == vec![F, T]);
            }
        }
    }

    #[test]
    fn two_cnf_is_unsat() {
        let result = run_cdcl(vec![vec![1, 2], vec![-1, -2], vec![1, -2]], 2);
        match result {
            UNSAT => (),
            SAT(_) => panic!("Expected UNSAT"),
        }
    }
}

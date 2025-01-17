use std::collections::HashSet;


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

fn remove_duplicates<T: Ord>(v: &mut Vec<T>){
    v.sort();     
    v.dedup();    // Remove duplicatas
}

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    println!("TODO: cdcl run {:?}", cnf);
    let mut solver = Cdcl::new(cnf, lits);
    solver.pre_process(); //aplica a regra PURE e outros truques de pré-processamento
    while true {
    //     while (propagate_gives_conflict()){
    //         if (decision_level==0) return UNSAT;
    //         else analyze_conflict();
    //     }
    //     restart_if_applicable();
    //     remove_lemmas_if_applicable();
    //     if (!decide()) returns SAT(self.format()); // All vars assigned
    }
    CdclResult::UNSAT
}

#[derive(Debug)]
struct OccurLists{
    positive: Vec<Vec<usize>>,// positive[k] contém os índices das cláusulas que têm o literal (k+1)
    negative: Vec<Vec<usize>>,// negative[k] contém os índices das cláusulas que têm o literal -(k+1)
}                        // indexação em base 0 😞😞😞

impl OccurLists{
    fn new() -> OccurLists{
        OccurLists{
            positive: vec![],
            negative: vec![],
        }
    }
}

#[derive(Debug)]
struct InnerAssignment{
    atom: usize,
    asgnm: Assignment,
    decision_level: usize,
}

struct Cdcl {
    partial_model: Vec<InnerAssignment>, // Vetor usado pelas regras,
    decision_points: Vec<usize>, // Se o valor k está nesse vetor, quer dizer que partial_model[k+1] está em um decision level acima de partial_model[k]
    clauses: Vec<Vec<i64>>, // array de cláusulas
    conflicting_literals: Vec<usize>,
    unassigned: HashSet<usize>, // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize, // total de átomos
    decision_level: usize, // maior nível de decisão do estado
    confliting: Option<Vec<i64>>, // cláusula conflitante
    occur_lists: OccurLists, 
}

impl Cdcl {
    fn new(cnf: Vec<Vec<i64>>, lits: usize) -> Cdcl {
        let n = cnf.len();
        Cdcl {
            partial_model: vec![],
            decision_points: vec![],
            clauses: cnf,
            conflicting_literals: vec![0;n],
            unassigned: (1..=lits).collect(),
            number_of_atoms: lits,
            decision_level: 0,
            confliting: None,
            occur_lists: OccurLists::new(),
        }
    }

    fn extend_partial_model(&mut self, atom: usize, asgnm: Assignment, decision_level: usize){
        let inner: InnerAssignment = InnerAssignment{
                                        atom,
                                        asgnm, 
                                        decision_level
                                    };
        if decision_level>self.decision_level{
            self.decision_level+=1;
            self.decision_points.push(self.partial_model.len()-1);
        }
        self.unassigned.remove(&atom);
        self.partial_model.push(inner);
    }

    fn pre_process(&mut self) -> () {
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_atoms];
        let mut unary_clause_assignments: HashSet<i64> = HashSet::new();
        for clause in self.clauses.iter_mut(){
            remove_duplicates(clause); // remove cláusulas repetidas
            //let mut clause_is_tautology = false;
            //let mut seen_in_clause: HashSet<i64> = HashSet::new();
            if clause.len()==1{ // se essa cláusula só tem um literal, então só atribuições que tornam esse literal verdadeiro podem ser 
                unary_clause_assignments.insert(clause[0]);
            }
            /*for lit in clause.iter(){ // procura cláusulas triviais
                if seen_in_clause.contains(&(-lit)){
                    clause_is_tautology = true;
                    break;
                } else {
                    seen_in_clause.insert(*lit);
                }
            }*/
            //if !clause_is_tautology{ 
            // Vou supor que não vão existir cláusulas triviais (ex: 1 -1 2 -4 0) em nossos casos de teste pelo bem da minha sanidade
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
           // }
        }
        for (index, status) in seen_status.iter().enumerate() {
            match status { //Aplica PURE
                Seen::Unseen => (),
                Seen::SeenPositive => self.extend_partial_model(index+1, Assignment::T, 0),
                Seen::SeenNegative => self.extend_partial_model(index+1, Assignment::F, 0),  
                Seen::SeenBoth => (),
            }
        }
        for unary in unary_clause_assignments.into_iter(){
            let asgnm = if unary < 0{
                                        Assignment::F
                                    } else if unary > 0 {
                                        Assignment::T
                                    } else {
                                        panic!("0 in clause!!!!\nThis is not a valid CNF")
                                    };
            self.extend_partial_model(unary.abs() as usize, asgnm,  0);
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
                atom: -lit as usize, 
                asgnm: Assignment::F, 
                decision_level: self.decision_level
            }
        } else {
            asgn = InnerAssignment{
                atom: lit as usize, 
                asgnm: Assignment::T, 
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

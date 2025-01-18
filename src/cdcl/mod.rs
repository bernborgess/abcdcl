use std::collections::HashSet;
use std::collections::VecDeque;

#[derive(Debug)]
struct OccurLists{
    positive: Vec<Vec<usize>>,// positive[k] contém os índices das cláusulas que têm o literal (k+1)
    negative: Vec<Vec<usize>>,// negative[k] contém os índices das cláusulas que têm o literal -(k+1)
}                             // indexação em base 0 😞😞😞

impl OccurLists{
    fn new(n: usize) -> OccurLists{
        OccurLists{
            positive: vec![Vec::new();n],
            negative: vec![Vec::new();n],
        }
    }
}

#[derive(Clone, Debug)]
enum Seen {
    Unseen,
    SeenPositive,
    SeenNegative,
    SeenBoth,
}

#[derive(Debug)]
struct InnerAssignment{
    atom: usize,
    asgnm: bool,
    decision_level: usize,
    decision: bool,
    propagated: bool,
}

#[derive(Debug)]
struct Clause{
    data: Vec<i64>,
    p1: usize,
    p2: usize,
}

impl Clause{
    pub fn new(arr: Vec<Vec<i64>>) -> Vec<Clause>{
        arr.into_iter()
            .map(|v| Clause {data: v, p1: 0, p2: 1 })
            .collect()
    }

    fn watch(&mut self, lit: i64) -> bool{
        
    }
}


enum clause_states{
    sat,
    unsat,
    unit,
    unresolved,
}



#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}

fn remove_duplicates<T: Ord>(v: &mut Vec<T>){
    v.sort();     
    v.dedup();
}

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    println!("TODO: cdcl run {:?}", cnf);
    let mut solver = Cdcl::new(cnf, lits);
    solver.pre_process(); //aplica a regra PURE e outros truques de pré-processamento
    //solver.propagate_trusted_assignment();
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


struct Cdcl {
    partial_model: Vec<InnerAssignment>, // Vetor usado pelas regras,
    decision_points: Vec<usize>, // Se o valor k está nesse vetor, quer dizer que partial_model[k+1] está em um decision level acima de partial_model[k]
    clauses_list: Vec<Clause>, // array de cláusulas
    unassigned: HashSet<usize>, // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize, // total de átomos
    decision_level: usize, // maior nível de decisão do estado
    confliting: Option<Vec<i64>>, // cláusula conflitante
    occur_lists: OccurLists, // lista de ocorrências
    model: Vec<Option<bool>>, //elemento k-1 é Some(true) se o átomo k for verdadeiro, Some(false) se for falso e None se não estiver atribuído
}

impl Cdcl {
    fn new(cnf: Vec<Vec<i64>>, atoms: usize) -> Cdcl {
        Cdcl {
            partial_model: vec![],
            decision_points: vec![],
            clauses_list: Clause::new(cnf),
            unassigned: (1..=atoms).collect(),
            number_of_atoms: atoms,
            decision_level: 0,
            confliting: None,
            occur_lists: OccurLists::new(0),
            model: vec![None;atoms],
        }
    }

    fn clause_status(&self, clause_ind: usize) -> clause_states{
        let mut values: Vec<Option<bool>> = vec![];
        let mut false_count: usize = 0;
        let mut true_in_values: bool = false;
        for &literal in &self.clauses_list[clause_ind].data{
            if self.unassigned.contains(&(literal as usize)) {
                values.push(None);
            } else {
                let assgnm: Option<bool> = self.model[(literal as usize)-1];
                values.push(assgnm);
                if assgnm==Some(false){
                    false_count+=1;
                } else if assgnm==Some(true){
                    true_in_values = true;
                }
            }
        }
        if true_in_values{
            clause_states::sat
        } else if false_count == values.len(){
            clause_states::unsat
        } else if false_count == values.len()-1{
            clause_states::unit
        } else {
            clause_states::unresolved
        }
    }

    fn extend_partial_model(&mut self, atom: usize, asgnm: bool, decision: bool){
        if decision {
            self.decision_level+=1;
            self.decision_points.push(self.partial_model.len()-1);
        }
        let decision_level = self.decision_level;
        let inner = InnerAssignment {
            atom,
            asgnm,
            decision_level,
            decision,
            propagated: false,
        };
        
        self.unassigned.remove(&atom);
        self.partial_model.push(inner);
        self.model[atom-1] = Some(asgnm);
    }

    // Remove duplicatas, realiza atribuições triviais (PURE e cláusulas unitárias) e constrói a occur_list
    fn pre_process(&mut self) -> () {
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_atoms];
        let mut unary_clause_assignments: HashSet<i64> = HashSet::new();
        let mut occur_lists = OccurLists::new(self.number_of_atoms);
        for (clause_ind, clause) in self.clauses_list.iter_mut().enumerate(){
            remove_duplicates(&mut clause.data); // remove cláusulas repetidas
            //let mut clause_is_tautology = false;
            //let mut seen_in_clause: HashSet<i64> = HashSet::new();
            if clause.data.len()==1{ // se essa cláusula só tem um literal, então só atribuições que tornam esse literal verdadeiro podem ser modelos
                unary_clause_assignments.insert(clause.data[0]);
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
                for (i, lit) in clause.data.iter().enumerate(){ 
                    if *lit<0{                        
                        let index = (-lit-1) as usize;
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        if i<2 {occur_lists.negative[index].push(clause_ind);}
                        seen_status[index] = match seen_status[index] {
                            Seen::Unseen => Seen::SeenNegative,
                            Seen::SeenPositive => Seen::SeenBoth,
                            Seen::SeenNegative => Seen::SeenNegative,
                            Seen::SeenBoth => Seen::SeenBoth,
                        };
                    } else if *lit > 0 {
                        let index = (lit - 1) as usize;
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        if i<2 {occur_lists.positive[index].push(clause_ind);}
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
                Seen::SeenPositive => self.extend_partial_model(index+1, true, false),
                Seen::SeenNegative => self.extend_partial_model(index+1, false, false),  
                Seen::SeenBoth => (),
            }
        }
        for unary in unary_clause_assignments.into_iter(){
            let asgnm: bool =   if unary < 0{
                                        false
                                } else if unary > 0 {
                                    true
                                } else {
                                    panic!("0 in clause!!!!\nThis is not a valid CNF")
                                };
            self.extend_partial_model(unary.abs() as usize, asgnm,  false);
        }
        self.occur_lists = occur_lists;
    }

    fn propagate_gives_conflict(&mut self) -> bool {
        self.propagate();
        return self.confliting != None
    }

    fn propagate(&mut self){
        let mut propagate_queue: VecDeque<i64> = VecDeque::new();
        for p in &self.partial_model{
            if p.asgnm{
                propagate_queue.push_back((p.atom as i64));
            } else {
                propagate_queue.push_back(-(p.atom as i64));
            }
        }
        while true{
            match &propagate_queue.pop_front(){
                None => self.decide(), //a fila está vazia
                &Some(current) => {
                    let clauses_to_watch: &Vec<usize> ;
                    let ind: usize;
                    if current > 0 {
                        ind = (current-1) as usize;
                        clauses_to_watch = &self.occur_lists.negative[ind];
                    } else if current<0 {
                        ind = (-current+1) as usize;
                        clauses_to_watch = &self.occur_lists.positive[ind];
                    } else {
                        panic!("0 não é um literal");
                    };
                    for c_ind in clauses_to_watch.iter(){
                        self.clauses_list[c_index].watch(lit);
                    }
                }
            };
        }
    }

    /*fn format(&self) -> Vec<Assignment> {
        println!("TODO: format");
        vec![]
    }*/

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
    //use Assignment::*;
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
                assert_eq!(assign[0], true);
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
                assert!(assign == vec![true, false] || assign == vec![false, true]);
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

use std::collections::HashSet;
use std::collections::VecDeque;
use rand::seq::IteratorRandom;
use rand::Rng;
use Watcher::*;
use CdclResult::*;


fn conflict_model(lit: i64, model: &Vec<Option<bool>>) -> bool{
    let ind: usize = (lit.abs()-1) as usize;
    let sgn = if lit<0 {
        false
    } else if lit>0 {
        true
    } else {
        panic!("0 não é um literal")
    };
    match model[ind]{
        None => false,
        Some(asgnm) => asgnm!=sgn,
    }
}

enum Watcher{
    Unit(i64),
    NowWatched(i64),
    Conflict,
}

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

    fn get(&self, n: i64) -> &Vec<usize>{
        if n<0{
            let ind = -(n+1) as usize;
            &self.negative[ind]
        } else {
            let ind = (n-1) as usize;
            &self.positive[ind]
        }
    }

    fn get_mut(&mut self, n: i64) -> &mut Vec<usize>{
        if n<0{
            let ind = -(n+1) as usize;
            &mut self.negative[ind]
        } else {
            let ind = (n-1) as usize;
            &mut self.positive[ind]
        }
    }

    fn add_lit_to_clause(&mut self, lit: i64, clause: usize){
        self.get_mut(lit).push(clause);
    }

    fn remove_clauses_from_lit(&mut self, clauses: &Vec<usize>, lit: i64){
        let mut lit_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_list = lit_list
            .drain(..)
            .filter(|x| !clauses.contains(x))
            .collect();
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
    lit: i64, //atom number with polarity, -1,1,-2,2..
    decision_level: usize,
    decision: bool, //true if assignment comes from a decide
}

#[derive(Clone, Debug)]
struct Clause{
    data: Vec<i64>,
    watch_ptr: [usize; 2],
}

impl Clause{
    pub fn new(arr: Vec<Vec<i64>>) -> Vec<Clause>{
        arr.into_iter()
            .map(|v| Clause {data: v, watch_ptr: [0, 1]})
            .collect()
    }

    fn watch(&mut self, lit: i64, model: &Vec<Option<bool>>) -> Watcher{//remove demo
        if self.data.len()==1{
            return Unit(lit)
        }
        let ind: usize = if self.point(0) == lit{
            0
        } else if self.point(1) == lit {
            1
        } else { 
            panic!("There's only 2 pointers")
        };
        let mut status: Watcher = self.next(ind);
        while self.boring(&status, model){
            status = self.next(ind)
        }
        status
    }

    fn boring(&self, status: &Watcher, model: &Vec<Option<bool>>) -> bool{
        match status{
            Unit(_) => false,
            Conflict => false,
            &NowWatched(lit) => {
                let index: usize;
                let polarity: bool;
                if lit < 0{
                    index = (-lit-1) as usize;
                    polarity = false;
                } else if lit>0 {
                    index = (lit-1) as usize;
                    polarity = true;
                } else {
                    panic!("0 is not a literal");
                }
                match model[index]{
                    None => false,
                    Some(asgmnt) => asgmnt!=polarity,
                }
            }
        }
    }

    fn point(&self, i: usize) -> i64{
        self.data[self.watch_ptr[i]]
    }

    fn next(&mut self, i: usize) -> Watcher{
        if self.watch_ptr[(i+1)%2]>=self.data.len(){
            return Conflict
        }
        let max_pointer = if self.watch_ptr[0]<self.watch_ptr[1] {
            self.watch_ptr[1]
        } else {
            self.watch_ptr[0]
        };
        
        self.watch_ptr[i] = max_pointer+1;
        if self.watch_ptr[i]==self.data.len(){// o ponteiro ultrapassa o array, retorna o literal que sobrou para ser propagado
            Unit(self.point((i+1)%2))
        } else {
            NowWatched(self.point(i))      // retorna o novo literal vigiado
        }
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
    let mut trivial = Some(solver.pre_process()); //aplica a regra PURE e outros truques de pré-processamento
    while true {
      while (solver.propagate_gives_conflict(&mut trivial, false)){
            if solver.decision_level==0 {
                return UNSAT;
            } else {
                solver.analyze_conflict();
            }
       }
        //restart_if_applicable();
        //remove_lemmas_if_applicable();
    //    if (!decide()) returns SAT(self.format()); // All vars assigned
    }
    CdclResult::UNSAT
}

pub fn run_demo(){
    let mut solver = Cdcl::new(vec![vec![1,-2,-6],vec![2,-3,5,-1,-6],vec![6,2,4],vec![1,2],vec![-6,-1,3],vec![-5,4,2]],6);
    solver.pre_process();
    solver.print_occur();
    solver.propagate_gives_conflict(&mut None, true);
}


pub struct Cdcl { //remove pub
    partial_model: Vec<InnerAssignment>, // Vetor usado pelas regras,
    decision_points: Vec<usize>, // Se o valor k está nesse vetor, quer dizer que partial_model[k] está em um decision level acima de partial_model[k-1]
    clauses_list: Vec<Clause>, // array de cláusulas
    unassigned: HashSet<usize>, // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize, // total de átomos
    pub decision_level: usize, // maior nível de decisão do estado
    conflicting: Option<Clause>, // cláusula conflitante
    occur_lists: OccurLists, // lista de ocorrências
    model: Vec<Option<bool>>, //elemento k-1 é Some(true) se o átomo k for verdadeiro, Some(false) se for falso e None se não estiver atribuído
    debug_decide: Vec<i64>,
}

impl Cdcl {
    pub fn new(cnf: Vec<Vec<i64>>, atoms: usize) -> Cdcl {
        Cdcl {
            partial_model: vec![],
            decision_points: vec![],
            clauses_list: Clause::new(cnf),
            unassigned: (1..=atoms).collect(),
            number_of_atoms: atoms,
            decision_level: 0,
            conflicting: None,
            occur_lists: OccurLists::new(0),
            model: vec![None;atoms],
            debug_decide: vec![-4,-2],
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

    fn extend_partial_model(&mut self, lit: i64, decision: bool){
        if decision {
            self.decision_level+=1;
            self.decision_points.push(self.partial_model.len());
        }
        let decision_level = self.decision_level;
        let inner = InnerAssignment {
            lit,
            decision_level,
            decision,
        };
        let atom = lit.abs() as usize;
        self.unassigned.remove(&atom);
        self.partial_model.push(inner);
        self.model[atom - 1] = if lit<0{
            Some(false)
        }else if lit>0{
            Some(true)
        }else{
            None
        };
    }

    fn update_model(&mut self, lit: i64){
        let atom = lit.abs() as usize;
        self.unassigned.remove(&atom);
        self.model[atom - 1] = if lit<0{
            Some(false)
        }else if lit>0{
            Some(true)
        }else{
            None
        };
    }

    // Remove duplicatas, realiza atribuições triviais (PURE e cláusulas unitárias) e constrói a occur_list
    pub fn pre_process(&mut self) -> VecDeque<i64>{// remove pub
        let mut propagation_queue: VecDeque<i64> = VecDeque::new();
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_atoms];
        let mut unary_clause_assignments: Vec<i64> = vec![]; // vector pois suponho que não existem 2 cláusulas unitárias iguais na entrada
        let mut occur_lists = OccurLists::new(self.number_of_atoms);
        for (clause_ind, clause) in self.clauses_list.iter_mut().enumerate(){
            //remove_duplicates(&mut clause.data); // remove cláusulas repetidas
            //let mut clause_is_tautology = false;
            //let mut seen_in_clause: HashSet<i64> = HashSet::new();
            if clause.data.len()==1{ // se essa cláusula só tem um literal, então só atribuições que tornam esse literal verdadeiro podem ser modelos
                unary_clause_assignments.push(clause.data[0]);
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
                for (i, &lit) in clause.data.iter().enumerate(){
                    let list = occur_lists.get_mut(lit); 
                    if lit<0{                        
                        let index = (-lit-1) as usize;
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        if i<2 {list.push(clause_ind);}
                        seen_status[index] = match seen_status[index] {
                            Seen::Unseen => Seen::SeenNegative,
                            Seen::SeenPositive => Seen::SeenBoth,
                            Seen::SeenNegative => Seen::SeenNegative,
                            Seen::SeenBoth => Seen::SeenBoth,
                        };
                    } else if lit > 0 {
                        let index = (lit-1) as usize;
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        if i<2 {list.push(clause_ind);}
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
                Seen::Unseen => propagation_queue.push_back((index+1) as i64), // se o átomo não aparece na fórmula posso atribuir o valor que eu quiser
                Seen::SeenPositive => propagation_queue.push_back((index+1) as i64),
                Seen::SeenNegative => propagation_queue.push_back(-((index+1) as i64)),  
                Seen::SeenBoth => (),
            }
        }
        for unary in unary_clause_assignments.into_iter(){
            if let Seen::SeenBoth = seen_status[(unary.abs() as usize)-1]{
                propagation_queue.push_back(unary);
            }
        }
        self.occur_lists = occur_lists;
        propagation_queue
    }

    pub fn propagate_gives_conflict(&mut self, trivial_lits: &mut Option<VecDeque<i64>>, demo: bool)->bool{ //remove pub
        let mut i = 1; //for demo
        //let mut update_model: Vec<i64> = vec![];
        let mut propagate_arr: VecDeque<(i64,bool)> = VecDeque::new();
        match trivial_lits{
            Some(q) => {
                while let Some(lit) = q.pop_front() {
                    propagate_arr.push_back((lit, false));
                    self.extend_partial_model(lit, false);
                }
            }
            None => ()
        };
        loop{
            /*let next = if demo{
                propagate_queue.pop_back()
            } else {
                propagate_queue.pop_front()
            };*/
            let next =  propagate_arr.pop_back();
            match next {
                None => {
                    let decided = if demo{
                        self.debug_decide.pop()
                    } else {
                        self.decide()
                    };
                    match decided{
                        Some(to_prop) => {
                            propagate_arr.push_back((to_prop,true));
                            //update_model.push(to_prop);
                            self.extend_partial_model(to_prop, true);
                        }
                        None => return false,
                    }
                },   //a fila está vazia
                Some((current, _)) => {
                    //self.extend_partial_model(current, decision);
                    let mut update_model: Vec<i64> = vec![];
                    let clauses_to_watch: &Vec<usize> = &self.occur_lists.get(-current);
                    let mut lit_saw = vec![];
                    let mut in_clause = vec![];
                    for &c_ind in clauses_to_watch.iter(){
                        match self.clauses_list[c_ind].watch(-current,&self.model){
                            NowWatched(new_watched) => {
                                lit_saw.push(new_watched);
                                in_clause.push(c_ind);
                            }
                            Unit(to_prop) => {
                                if conflict_model(to_prop,&self.model){
                                    self.conflicting = Some(self.clauses_list[c_ind].clone());
                                    return true;
                                }
                                propagate_arr.push_back((to_prop,false));
                                update_model.push(to_prop);
                            }
                            Conflict => {
                                self.conflicting = Some(self.clauses_list[c_ind].clone());
                                return true;
                            }
                        }
                    }
                    for &new_info in update_model.iter(){
                        //self.update_model(new_info);
                        self.extend_partial_model(new_info, false);
                    }
                    for i in 0..lit_saw.len() {
                        self.occur_lists.add_lit_to_clause(lit_saw[i], in_clause[i]);
                    }
                    self.occur_lists.remove_clauses_from_lit(&in_clause,-current);
                    if demo{
                        println!("\n iteration {i}");
                        self.print_model();
                        self.print_occur();
                        self.print_prop(&propagate_arr);
                        i+=1;
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

    fn decide(&self) -> Option<(i64)>{
        let mut rng = rand::thread_rng();
        let at: Option<&usize> = self.unassigned.iter().choose(&mut rng);
        let polarity: bool = rng.gen();
        if let Some(&atom) = at{
            if polarity{
                Some(atom as i64)
            } else {
                Some(-(atom as i64))
            }
        } else {
            None
        }
    }

    pub fn print_occur(&self){
        for (i, pos) in self.occur_lists.positive.iter().enumerate(){
            let v: Vec<usize> = pos.iter().map(|x| x+1).collect();
            println!("p{:?}: {:?}",i+1,v);
        }
        for (i, neg) in self.occur_lists.negative.iter().enumerate(){
            let v: Vec<usize> = neg.iter().map(|x| x+1).collect();
            println!("¬p{:?}: {:?}",i+1,v);
        }
    }

    pub fn print_model(&self){
        let mut s = "".to_string();
        for m in self.partial_model.iter(){
            if m.decision{
                s += &"• ".to_string();
            }
            if m.lit<0{
                s += &"¬".to_string();
            }
            s += &format!("p{:?} ",m.lit.abs());
        }
        println!("{:?}",s);
    }

    pub fn print_prop(&self, prop: &VecDeque<(i64,bool)>){
        let v: Vec<_> = prop.iter().map(|(x,b)| x).collect();
        println!("to propagate: {:?}", v)
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

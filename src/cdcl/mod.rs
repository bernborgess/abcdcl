// use indexmap::IndexSet;
use rand::seq::IteratorRandom;
use rand::Rng;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt;
use std::mem;
use CdclResult::*;
use Watcher::*;

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    println!("TODO: cdcl run {:?}", cnf);
    let mut solver: Cdcl = Cdcl::new(lits);
    let mut trivial: Option<VecDeque<i64>> = solver.pre_process(cnf); //aplica a regra PURE e outros truques de pré-processamento
    solver.build_occur_lists();
    while true {
        while (solver.propagate_gives_conflict(&mut trivial, false)) {
            if solver.decision_level == 0 {
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

//Qualquer adição ao modelo deve usar essa função ou a homônima pois o tipo do modelo pode ser refatorado
//ela checa se há contradição ou se um literal inválido está sendo adicionado
fn model_insert(model: &mut Vec<Option<bool>>, lit: i64) -> bool {
    let atom = lit.unsigned_abs() as usize;
    match model[atom] {
        Some(true) => {
            if lit > 0 {
                return true;
            } else if lit < 0 {
                return false;
            } else {
                panic!("0 is not a literal")
            }
        }
        Some(false) => {
            if lit < 0 {
                return true;
            } else if lit > 0 {
                return false;
            } else {
                panic!("0 is not a literal")
            }
        }
        None => {
            model[atom] = if lit > 0 {
                Some(true)
            } else if lit < 0 {
                Some(false)
            } else {
                panic!("0 is not a literal")
            };
        }
    }
    true
}

fn model_disagrees(model: &Vec<Option<bool>>, lit: i64) -> bool {
    match model[lit.unsigned_abs() as usize] {
        Some(b) => b != (lit > 0),
        None => false,
    }
}

enum Watcher {
    Unit(i64),
    NewWatched(i64),
    Conflict,
}

/*impl Watcher{
    fn unwrap(&self)->i64{
        match self{
            &Unit(v) => v,
            &WatchedFromTo(from,to) => (from,to),
            Conflict => panic!("Unwrap on conflict")
        }
    }
}*/

#[derive(Debug, Default)]
struct OccurLists {
    positive: Vec<Vec<usize>>, // positive[k] contém os índices das cláusulas que têm o literal +k vigiado
    negative: Vec<Vec<usize>>, // negative[k] contém os índices das cláusulas que têm o literal -k vigiado
}

impl OccurLists {
    fn new(n: usize) -> OccurLists {
        OccurLists {
            positive: vec![Vec::new(); n + 1], //aloco 1 espaço a mais para garantir indexação em base 1
            negative: vec![Vec::new(); n + 1],
        }
    }

    fn take(&mut self, lit: i64) -> Vec<usize> {
        if lit < 0 {
            mem::take(&mut self.negative[lit.unsigned_abs() as usize])
        } else {
            mem::take(&mut self.positive[lit.unsigned_abs() as usize])
        }
    }

    fn give_to(&mut self, clause_lists: Vec<usize>, lit: i64) {
        if lit < 0 {
            self.negative[lit.unsigned_abs() as usize] = clause_lists;
        } else {
            self.positive[lit.unsigned_abs() as usize] = clause_lists;
        }
    }

    fn get(&self, lit: i64) -> &Vec<usize> {
        if lit < 0 {
            &self.negative[lit.unsigned_abs() as usize]
        } else {
            &self.positive[lit.unsigned_abs() as usize]
        }
    }

    fn get_mut(&mut self, lit: i64) -> &mut Vec<usize> {
        if lit < 0 {
            &mut self.negative[lit.unsigned_abs() as usize]
        } else {
            &mut self.positive[lit.unsigned_abs() as usize]
        }
    }

    fn add_clause_to_lit(&mut self, clause: usize, lit: i64) {
        self.get_mut(lit).push(clause);
    }

    fn remove_clauses_from_lit(&mut self, clauses: &Vec<usize>, lit: i64) {
        let mut lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list
            .drain(..)
            .filter(|x| !clauses.contains(x))
            .collect();
    }

    fn remove_clause_from_lit(&mut self, clause: usize, lit: i64) {
        let mut lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list.drain(..).filter(|&x| clause != x).collect();
    }
}

#[derive(Clone, Debug)]
enum Seen {
    Unseen,
    Positive,
    Negative,
    Both,
}

#[derive(Debug)]
struct InnerAssignment {
    lit: i64, //atom number with polarity, -1,1,-2,2..
    decision_level: usize,
    antecedent: Option<usize>,
    decision: bool, //true if assignment comes from a decide
}

#[derive(Clone)]
pub struct Clause {
    data: Vec<i64>,
    watch_ptr: [usize; 2],
    status: ClauseStates,
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Define how you want your struct to be printed
        write!(f, "{:?}", self.data)
    }
}

impl Clause {
    pub fn new(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| Clause {
                data: v,
                watch_ptr: [0, 1],
                status: ClauseStates::Unresolved,
            })
            .collect()
    }

    fn watch(&mut self, lit: i64, model: &Vec<Option<bool>>) -> Watcher {
        if self.data.len() == 1 {
            return Unit(lit);
        }
        let ind: usize = if self.point(0) == lit {
            //seleciona o ponteiro que vai ser movido
            0
        } else if self.point(1) == lit {
            1
        } else {
            panic!("There's only 2 pointers")
        };
        //posição inicial do ponteiro para caso ele tenha que andar mais de uma vez
        let start = self.point(ind);

        //move o ponteiro
        let mut status: Watcher = self.next(ind);

        //se não encontrar uma cláusula unitária, checa o novo literal vigiado
        //se o novo literal vigiado for falseado pelo modelo, move o ponteiro de novo
        //se o novo literal vigiado for satisfeito pelo modelo, para de vigiar a cláusula
        let mut sat_or_unsat = self.satisfied_or_falsified(&status, model);
        while let Some(false) = &sat_or_unsat {
            status = self.next(ind);
            sat_or_unsat = self.satisfied_or_falsified(&status, model);
        }

        match &status{
            &Watcher::Unit(to_prop) => self.status = ClauseStates::Unit(to_prop),
            &Watcher::NewWatched(new_lit) => {
                match sat_or_unsat{
                    Some(true) => self.status = ClauseStates::Satisfied(new_lit),
                    Some(false) => panic!("This should be impossible. The pointer should move until this turn into Unit or find a non-falsified literal"),
                    None => self.status = ClauseStates::Unresolved,
                }
            }
            Watcher::Conflict => panic!("Should be dead"),
        }
        status
    }

    //Some(true) se satisfeito, Some(false) se falseado, None se não atribuído ou se é Unidade ou Conflito
    fn satisfied_or_falsified(&self, status: &Watcher, model: &Vec<Option<bool>>) -> Option<bool> {
        match status {
            Watcher::Unit(_) => None,
            Watcher::Conflict => None,
            &Watcher::NewWatched(to) => {
                let polarity: bool = if to < 0 {
                    false
                } else if to > 0 {
                    true
                } else {
                    panic!("0 is not a literal");
                };
                match model[to.abs() as usize] {
                    None => None,
                    Some(asgmnt) => Some(asgmnt == polarity),
                }
            }
        }
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> i64 {
        self.data[self.watch_ptr[i]]
    }

    fn next(&mut self, i: usize) -> Watcher {
        // Se o outro ponteiro já tiver explodido, retorna conflito
        if self.watch_ptr[(i + 1) % 2] >= self.data.len() {
            return Conflict; //Isso deve ser código morto, mas vou deixar essa linha pra detectar bug
        }
        let max_pointer = if self.watch_ptr[0] < self.watch_ptr[1] {
            self.watch_ptr[1]
        } else {
            self.watch_ptr[0]
        };
        //nova posição para onde o ponteiro i vai apontar
        self.watch_ptr[i] = max_pointer + 1;

        // caso ponteiro ultrapasse o array, retorna o literal que sobrou no outro ponteiro para ser propagado
        if self.watch_ptr[i] == self.data.len() {
            self.status = ClauseStates::Unit(self.point((i + 1) % 2));
            Unit(self.point((i + 1) % 2))
        } else {
            NewWatched(self.point(i)) // retorna o novo literal vigiado
        }
    }
}

#[derive(Clone, Debug)]
enum ClauseStates {
    Satisfied(i64),
    Falsified(i64),
    Unit(i64),
    Unresolved,
}

#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}

fn remove_duplicates<T: Ord>(v: &mut Vec<T>) {
    v.sort();
    v.dedup();
}

pub fn run_demo() {
    let mut solver: Cdcl = Cdcl::new(6);
    let cnf: Vec<Vec<i64>> = vec![
        vec![1, -2, -6],
        vec![2, -3, 5, -1, -6],
        vec![6, 2, 4],
        vec![1, 2],
        vec![-6, -1, 3],
        vec![-5, 4, 2],
    ];
    solver.pre_process(cnf);
    solver.print_occur();
    solver.propagate_gives_conflict(&mut None, true);
}

pub struct Cdcl {
    //remove pub
    partial_model: Vec<InnerAssignment>, // Vetor usado pelas regras,
    decision_points: Vec<usize>, // Se o valor k está nesse vetor, quer dizer que partial_model[k] está em um decision level acima de partial_model[k-1]
    pub clauses_list: Vec<Clause>, // array de cláusulas
    unassigned: HashSet<usize>,  // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize,      // total de átomos
    pub decision_level: usize,   // maior nível de decisão do estado
    conflicting: Option<Clause>, // cláusula conflitante
    occur_lists: OccurLists,     //lista de ocorrências
    model: Vec<Option<bool>>, //elemento k é Some(true) se o átomo k for verdadeiro, Some(false) se for falso e None se não estiver atribuído
    debug_decide: Vec<i64>,
}

impl Cdcl {
    pub fn new(atoms: usize) -> Cdcl {
        Cdcl {
            partial_model: vec![],
            decision_points: vec![],
            clauses_list: vec![],
            unassigned: (1..=atoms).collect(),
            number_of_atoms: atoms,
            decision_level: 0,
            conflicting: None,
            occur_lists: OccurLists::new(0),
            model: vec![None; atoms + 1], //aloco 1 espaço a mais para garantir indexação em base 1
            debug_decide: vec![-4, -2],
        }
    }

    fn conflict_model(&self, lit: i64) -> bool {
        let ind: usize = lit.unsigned_abs() as usize;
        let sign = if lit < 0 {
            false
        } else if lit > 0 {
            true
        } else {
            panic!("0 não é um literal")
        };
        match self.model[ind] {
            None => false,
            Some(assignment) => assignment != sign,
        }
    }

    // Remove duplicatas, realiza atribuições triviais (PURE e cláusulas unitárias), remove cláusulas satisfeitas
    // retorna vetor de i64 para propagar e constrói as cláusulas do solver
    pub fn pre_process(&mut self, mut cnf: Vec<Vec<i64>>) -> Option<VecDeque<i64>> {
        let mut decided: VecDeque<i64> = VecDeque::new();
        let mut clauses_to_remove: HashSet<usize> = HashSet::new();
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_atoms + 1]; // 1 campo extra para indexar em base 1
                                                                                       //let mut unary_clause_assignments: Vec<i64> = vec![]; // vector pois suponho que não existem 2 cláusulas unitárias iguais na entrada
        let mut full_occur_lists = OccurLists::new(self.number_of_atoms + 1); // 1 campo extra para indexar em base 1
        for (clause_ind, clause) in cnf.iter_mut().enumerate() {
            //println!("Clause {:?}: {:?}", clause_ind, &clause);
            //println!("{}",3);
            //remove_duplicates(&mut clause.data); // remove cláusulas repetidas
            //let mut clause_is_tautology = false;
            //let mut seen_in_clause: HashSet<i64> = HashSet::new();
            if clause.len() == 1 {
                // se essa cláusula só tem um literal, então só atribuições que tornam esse literal verdadeiro podem ser modelos
                if clause[0] == 0 {
                    panic!("0 is not a literal");
                }
                decided.push_back(clause[0]);
                clauses_to_remove.insert(clause_ind);
                //println!("By reason of length 1: ");
                //println!("decided: {:?}",&decided);
                //println!("clauses to remove: {:?}", &clauses_to_remove);
            }
            /*for lit in clause.iter(){ // procura cláusulas triviais
                if seen_in_clause.contains(&(-lit)){
                    clause_is_tautology = true;
                    break;
                } else {
                    seen_in_clause.insert(*lit);
                }
            }*/
            // Vou supor que não vão existir cláusulas triviais (ex: 1 -1 2 -4 0) em nossos casos de teste pelo bem da minha sanidade
            for &lit in clause.iter() {
                let mut full_list = full_occur_lists.get_mut(lit);
                let atom = lit.unsigned_abs() as usize;
                if lit < 0 {
                    // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                    full_list.push(clause_ind);
                    seen_status[atom] = match seen_status[atom] {
                        Seen::Unseen => Seen::Negative,
                        Seen::Positive => Seen::Both,
                        Seen::Negative => Seen::Negative,
                        Seen::Both => Seen::Both,
                    };
                } else if lit > 0 {
                    // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                    full_list.push(clause_ind);
                    seen_status[atom] = match seen_status[atom] {
                        Seen::Unseen => Seen::Positive,
                        Seen::Positive => Seen::Positive,
                        Seen::Negative => Seen::Both,
                        Seen::Both => Seen::Both,
                    };
                } else {
                    panic!("0 in clause!!!!\nThis is not a valid CNF");
                }
            }
        }
        for (index, status) in seen_status.iter().enumerate().skip(1) {
            //check
            match status {
                //Aplica PURE
                Seen::Unseen => decided.push_back((index) as i64), // se o átomo não aparece na fórmula posso atribuir o valor que eu quiser
                Seen::Positive => decided.push_back((index) as i64),
                Seen::Negative => decided.push_back(-(index as i64)),
                Seen::Both => (),
            }
        }
        match self.grow_model_and_remove_clauses(
            &decided,
            &mut clauses_to_remove,
            &mut full_occur_lists,
            cnf,
        ) {
            None => {
                //Unsat case
                //panic!("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");//remover
                None
            }
            Some(filtered_cnf) => {
                self.clauses_list = Clause::new(filtered_cnf);
                Some(decided)
            }
        }
    }

    pub fn build_occur_lists(&mut self) {
        let mut occur_lists = OccurLists::new(self.number_of_atoms);
        for (c_ind, c) in self.clauses_list.iter().enumerate() {
            for &lit in c.data.iter().take(2) {
                occur_lists.add_clause_to_lit(c_ind, lit);
            }
        }
        self.occur_lists = occur_lists;
    }

    fn grow_model_and_remove_clauses(
        &mut self,
        decided: &VecDeque<i64>,
        clauses_to_remove: &mut HashSet<usize>,
        full_occur_lists: &OccurLists,
        mut cnf: Vec<Vec<i64>>,
    ) -> Option<Vec<Vec<i64>>> {
        for &lit in decided.iter() {
            if !self.model_insert(lit) {
                return None; //Unsat case
            }
            let occurs = full_occur_lists.get(lit);
            for &clause_ind in occurs.iter() {
                clauses_to_remove.insert(clause_ind);
            }
        }
        cnf = cnf
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !clauses_to_remove.contains(i))
            .map(|(_, item)| item)
            .collect();
        Some(cnf)
    }

    //Qualquer adição ao modelo deve usar essa função ou a homônima pois o tipo do modelo pode ser refatorado
    //ela checa se há contradição ou se um literal inválido está sendo adicionado
    fn model_insert(&mut self, lit: i64) -> bool {
        let atom = lit.unsigned_abs() as usize;
        match &self.model[atom] {
            Some(true) => {
                if lit > 0 {
                    ();
                } else if lit < 0 {
                    return false;
                } else {
                    panic!("0 is not a literal")
                }
            }
            Some(false) => {
                if lit < 0 {
                    ();
                } else if lit > 0 {
                    return false;
                } else {
                    panic!("0 is not a literal")
                }
            }
            None => {
                self.model[atom] = if lit > 0 {
                    Some(true)
                } else if lit < 0 {
                    Some(false)
                } else {
                    panic!("0 is not a literal")
                };
            }
        }
        true
    }

    pub fn propagate_gives_conflict(
        &mut self,
        trivial_lits_ref: &mut Option<VecDeque<i64>>,
        demo: bool,
    ) -> bool {
        let mut i = 1; //for demo

        //arranco o modelo do solver para resolver conflitos com o borrow checker
        let mut model = mem::take(&mut self.model);
        let mut occur_lists = &mut self.occur_lists;
        let mut trivial_lits: Option<VecDeque<i64>> = trivial_lits_ref.take();
        let mut propagate_arr: VecDeque<i64> = match trivial_lits {
            Some(q) => q,
            None => VecDeque::new(),
        };
        loop {
            match propagate_arr.pop_front() {
                None => {
                    self.model = model;
                    return false;
                } //a fila está vazia, não tem nada para propagar
                Some(current) => {
                    //self.extend_partial_model(current, decision);
                    //let mut update_model: Vec<i64> = vec![];
                    let clauses_to_watch: Vec<usize> = occur_lists.take(-current);
                    for &c_ind in clauses_to_watch.iter() {
                        match self.clauses_list[c_ind].watch(-current, &self.model) {
                            // no unit found
                            NewWatched(new_watched) => {
                                //self.occur_lists.remove_clause_from_lit(c_ind, -current);
                                occur_lists.add_clause_to_lit(c_ind, new_watched)
                            }
                            Unit(to_prop) => {
                                // checa se to_prop é conflitante com o modelo
                                if model_disagrees(&model, to_prop) {
                                    self.conflicting = Some(self.clauses_list[c_ind].clone());
                                    self.model = model;
                                    occur_lists.give_to(clauses_to_watch, -current);
                                    return true;
                                }
                                propagate_arr.push_back(to_prop);
                                model_insert(&mut model, to_prop);
                            }
                            Conflict => {
                                /*self.conflicting = Some(self.clauses_list[c_ind].clone());
                                return true;*/
                                panic!("Isso devia ser código morto");
                            }
                        }
                    }
                    occur_lists.give_to(clauses_to_watch, -current);
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

    fn decide(&self) -> Option<i64> {
        let mut rng = rand::thread_rng();
        let at: Option<&usize> = self.unassigned.iter().choose(&mut rng);
        let polarity: bool = rng.gen();
        if let Some(&atom) = at {
            if polarity {
                Some(atom as i64)
            } else {
                Some(-(atom as i64))
            }
        } else {
            None
        }
    }

    pub fn print_occur(&self) {
        for (i, pos) in self.occur_lists.positive.iter().enumerate() {
            let v: Vec<usize> = pos.iter().map(|x| x + 1).collect();
            println!("p{:?}: {:?}", i + 1, v);
        }
        for (i, neg) in self.occur_lists.negative.iter().enumerate() {
            let v: Vec<usize> = neg.iter().map(|x| x + 1).collect();
            println!("¬p{:?}: {:?}", i + 1, v);
        }
    }

    pub fn print_model(&self) {
        let mut s = "".to_string();
        for m in self.partial_model.iter() {
            if m.decision {
                s += "• ";
            }
            if m.lit < 0 {
                s += "¬";
            }
            s += &format!("p{:?} ", m.lit.unsigned_abs());
        }
        println!("{:?}", s);
    }

    pub fn print_prop(&self, prop: &VecDeque<i64>) {
        let v: Vec<_> = prop.iter().map(|x| x).collect();
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
                assert!(assign[0]);
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

    #[test]
    fn pre_process_can_solve() {
        let mut solver: Cdcl = Cdcl::new(6);
        let original_cnf: Vec<Vec<i64>> = vec![
            //every clause has 1 (verified by pure) or 4 (verified by unit clause)
            vec![1, 4],
            vec![1, -2, -6],
            vec![2, -3, 5, 1, -6],
            vec![6, 2, -4],
            vec![1, 2],
            vec![-6, 1, 3],
            vec![-5, -4, 2],
            vec![-4],
            vec![1, 2, 3],
        ];
        let target_cnf: Vec<Vec<i64>> = vec![];
        solver.pre_process(original_cnf);
        for (i, c) in solver.clauses_list.iter().enumerate() {
            for (j, &lit) in c.data.iter().enumerate() {
                assert_eq!(lit, target_cnf[i][j]);
            }
        }
    }

    #[test]
    fn pre_process_worked() {
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
        for (i, c) in solver.clauses_list.iter().enumerate() {
            for (j, &lit) in c.data.iter().enumerate() {
                assert_eq!(lit, target_cnf[i][j]);
            }
        }
    }
}

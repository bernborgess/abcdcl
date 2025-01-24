use assignment::Assignment;
use clause::{Clause, Watcher::*};
use occurlist::OccurLists;
use rand::{seq::IteratorRandom, Rng};
use std::cmp::Ordering;
use std::collections::{HashSet, VecDeque};
use std::mem;
use utils::{get_sign, print_model};
use CdclResult::*;

pub mod assignment;
pub mod clause;
pub mod occurlist;
pub mod utils;

// TODO: Change cnf data structure
pub fn run_cdcl(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    // eprintln!("TODO: cdcl run {:?}", cnf);
    let mut solver: Cdcl = Cdcl::new(lits);
    let mut trivial_or_decided: Option<VecDeque<i64>> = solver.pre_process(cnf); //aplica a regra PURE e outros truques de pré-processamento
    if solver.clauses_list.is_empty() {
        return solver.yield_model();
    }
    solver.build_occur_lists();
    loop {
        while solver.propagate_gives_conflict(&mut trivial_or_decided) {
            if solver.decision_level == 0 {
                return UNSAT;
            } else {
                let b = solver.analyze_conflict();
            }
        }
        //restart_if_applicable();
        //remove_lemmas_if_applicable();
        match solver.decide() {
            None => return solver.yield_model(),
            Some(a) => trivial_or_decided = Some(VecDeque::from(vec![a])),
        }
    }
}

pub fn run_cdcl_debug(cnf: Vec<Vec<i64>>, lits: usize) -> CdclResult {
    // eprintln!("TODO: cdcl run {:?}", cnf);
    let mut solver: Cdcl = Cdcl::new(lits);
    let mut trivial_or_decided: Option<VecDeque<i64>> = None; //aplica a regra PURE e outros truques de pré-processamento
    solver.clauses_list = Clause::new_vec(cnf);
    if solver.clauses_list.is_empty() {
        return solver.yield_model();
    }
    solver.build_occur_lists();
    loop {
        while solver.propagate_gives_conflict(&mut trivial_or_decided) {
            if solver.decision_level == 0 {
                return UNSAT;
            } else {
                let dl_target = solver.analyze_conflict();
                //solver.backjump(dl_target);
            }
        }
        //restart_if_applicable();
        //remove_lemmas_if_applicable();
        match solver.debug_decide() {
            None => return solver.yield_model(),
            Some(a) => trivial_or_decided = Some(VecDeque::from(vec![a])),
        }
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

#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}

fn remove_duplicates<T: Ord>(v: &mut Vec<T>) {
    v.sort();
    v.dedup();
}

pub struct Cdcl {
    //remove pub
    //partial_model: Vec<InnerAssignment>, // Vetor usado pelas regras,
    //decision_points: Vec<usize>, // Se o valor k está nesse vetor, quer dizer que partial_model[k] está em um decision level acima de partial_model[k-1]
    pub clauses_list: Vec<Clause>,  // array de cláusulas
    unassigned: HashSet<usize>,     // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize,         // total de átomos
    pub decision_level: usize,      // maior nível de decisão do estado
    conflicting: Option<Clause>,    // cláusula conflitante
    occur_lists: OccurLists,        //lista de ocorrências
    model: Vec<Option<Assignment>>, //elemento k é Some(true) se o átomo k for verdadeiro, Some(false) se for falso e None se não estiver atribuído
    debug_decisions: Vec<i64>,
}

impl Cdcl {
    pub fn new(atoms: usize) -> Cdcl {
        Cdcl {
            //partial_model: vec![],
            //decision_points: vec![],
            clauses_list: vec![],
            unassigned: (1..=atoms).collect(),
            number_of_atoms: atoms,
            decision_level: 0,
            conflicting: None,
            occur_lists: OccurLists::new(0),
            model: vec![None; atoms + 1], //aloco 1 espaço a mais para garantir indexação em base 1
            debug_decisions: vec![-4, -2],
        }
    }

    fn conflict_model(&self, lit: i64) -> bool {
        let ind: usize = lit.unsigned_abs() as usize;
        match &self.model[ind] {
            None => false,
            Some(assignment) => assignment.polarity != get_sign(lit),
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
            //eprintln!("Clause {:?}: {:?}", clause_ind, &clause);
            //eprintln!("{}",3);
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
                //eprintln!("By reason of length 1: ");
                //eprintln!("decided: {:?}",&decided);
                //eprintln!("clauses to remove: {:?}", &clauses_to_remove);
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
                let full_list = full_occur_lists.get_mut(lit);
                let atom = lit.unsigned_abs() as usize;
                match lit.cmp(&0) {
                    Ordering::Less => {
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        full_list.push(clause_ind);
                        seen_status[atom] = match seen_status[atom] {
                            Seen::Unseen => Seen::Negative,
                            Seen::Positive => Seen::Both,
                            Seen::Negative => Seen::Negative,
                            Seen::Both => Seen::Both,
                        };
                    }
                    Ordering::Greater => {
                        // aproveito que estou iterando sobre as cláusulas para preencher as listas de ocorrência
                        full_list.push(clause_ind);
                        seen_status[atom] = match seen_status[atom] {
                            Seen::Unseen => Seen::Positive,
                            Seen::Positive => Seen::Positive,
                            Seen::Negative => Seen::Both,
                            Seen::Both => Seen::Both,
                        };
                    }
                    Ordering::Equal => panic!("0 in clause - This is not a valid CNF"),
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
                self.clauses_list = Clause::new_vec(filtered_cnf);
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
            if !self.model_insert(lit, None) {
                return None; //Unsat case
            }
            self.unassigned.remove(&(lit.unsigned_abs() as usize));
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

    //TODO: Test
    pub fn propagate_gives_conflict(
        &mut self,
        trivial_or_decided_ref: &mut Option<VecDeque<i64>>,
    ) -> bool {
        //arranco o modelo do solver para resolver conflitos com o borrow checker
        let mut model: Vec<Option<Assignment>> = mem::take(&mut self.model);
        //print_model(&model);
        //self.f();
        let occur_lists: &mut OccurLists = &mut self.occur_lists;
        let trivial_or_decided: Option<VecDeque<i64>> = trivial_or_decided_ref.take();
        //println!("trivial_or_decided: {:?}", &trivial_or_decided);
        let mut propagate_arr: VecDeque<i64> = trivial_or_decided.unwrap_or_default();
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
                    //println!("occur_list[{:?}] = {:?}", -current, &clauses_to_watch);
                    for &c_ind in clauses_to_watch.iter() {
                        //println!("Clause {c_ind}:{:?}", self.clauses_list[c_ind]);
                        match self.clauses_list[c_ind].watch(-current, &model) {
                            // no unit found
                            NewWatched(new_watched) => {
                                //self.occur_lists.remove_clause_from_lit(c_ind, -current);
                                occur_lists.add_clause_to_lit(c_ind, new_watched)
                            }
                            //AlreadyWatched(lit) => (),
                            Unit(to_prop) => {
                                // checa se to_prop é conflitante com o modelo
                                match Cdcl::model_opinion(&model, to_prop) {
                                    Some(false) => {
                                        //probably dead code
                                        self.conflicting = Some(self.clauses_list[c_ind].clone());
                                        self.model = model;
                                        occur_lists.give_to(clauses_to_watch, -current);
                                        return true;
                                    }
                                    Some(true) => (),
                                    None => {
                                        self.unassigned.remove(&(to_prop.unsigned_abs() as usize));
                                        propagate_arr.push_back(to_prop);
                                        Cdcl::model_insert_static(
                                            &mut model,
                                            to_prop,
                                            Some(c_ind),
                                            self.decision_level,
                                        );
                                    }
                                }
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

    fn model_opinion(model: &[Option<Assignment>], lit: i64) -> Option<bool> {
        model[lit.unsigned_abs() as usize].map(|b| b.polarity == (lit > 0))
    }

    /*fn format(&self) -> Vec<Assignment> {
        eprintln!("TODO: format");
        vec![]
    }*/

    /// Returns what decision level needs to be decremented
    fn analyze_conflict(&self) -> Option<(usize, Clause)> {
        if self.decision_level == 0 {
            return None;
        }

        let mut learnt = self
            .conflicting
            .as_ref()
            .expect("Conflict was not defined!")
            .clone();

        // literals with current decision level
        let mut literals: Vec<i64> = learnt
            .data
            .iter()
            .filter(|lit| self.literal_has_max_dl(**lit))
            .copied()
            .collect();

        while literals.len() != 1 {
            // Implied literals
            literals.retain(|lit| {
                let lit_idx = lit.unsigned_abs() as usize;
                self.model[lit_idx]
                    .expect("Conflict should be assigned for all variables")
                    .antecedent
                    .is_some()
            });

            // Select any literal that meets the criterion
            let literal = literals.first();
            if literal.is_none() {
                break;
            }
            let literal = *literal.unwrap();
            let antecedent = &self.get_antecedent(literal);
            if antecedent.is_none() {
                break;
            }
            let antecedent = &self.clauses_list[antecedent.unwrap()];
            learnt = learnt.resolution(antecedent, literal.unsigned_abs() as usize);

            // Literals with current decision level
            literals = learnt
                .data
                .iter()
                .filter(|lit| self.literal_has_max_dl(**lit))
                .copied()
                .collect();
        }

        // out of the loop, `learnt` is now the new clause
        // compute the backtrack level b (second largest decision level)
        let mut b = 0;
        for lit in &learnt.data {
            if self.literal_has_max_dl(*lit) {
                continue;
            }
            b = std::cmp::max(b, self.literal_get_dl(*lit));
        }
        Some((b, learnt))
    }

    /// Returns index of clause that propagated this literal
    fn get_antecedent(&self, lit: i64) -> Option<usize> {
        self.model[lit.unsigned_abs() as usize]?.antecedent
    }

    /// Add a new clause and prepares the watched literals
    fn add_clause(&mut self, data: Vec<i64>) {
        let new_clause_id = self.clauses_list.len();

        // Update occurlist
        let lit1 = data[0];
        let lit2 = data[1];

        self.occur_lists.add_clause_to_lit(new_clause_id, lit1);
        self.occur_lists.add_clause_to_lit(new_clause_id, lit2);

        // Add clause to problem
        let learnt_clause = Clause::new(data);
        self.clauses_list.push(learnt_clause);
    }

    fn literal_is_undefined(&self, lit: i64) -> bool {
        self.model[lit.unsigned_abs() as usize].is_none()
    }

    fn literal_get_dl(&self, lit: i64) -> usize {
        if let Some(ass) = self.model[lit.unsigned_abs() as usize] {
            ass.dl
        } else {
            0
        }
    }

    fn literal_has_dl(&self, lit: i64, dl: usize) -> bool {
        if self.literal_is_undefined(lit) {
            return false;
        }
        let actual_dl = self.literal_get_dl(lit);
        actual_dl == dl
    }

    fn literal_has_max_dl(&self, lit: i64) -> bool {
        self.literal_has_dl(lit, self.decision_level)
    }

    fn restart_if_applicable(&self) {
        eprintln!("TODO: restart_if_applicable");
    }

    fn remove_lemmas_if_applicable(&self) {
        eprintln!("TODO: remove_lemmas_if_applicable");
    }

    fn decide(&mut self) -> Option<i64> {
        let mut rng = rand::thread_rng();
        let at: Option<&usize> = self.unassigned.iter().choose(&mut rng);
        let polarity: bool = rng.gen();
        self.decision_level += 1;
        if let Some(&atom) = at {
            self.unassigned.remove(&atom);
            if polarity {
                println!("decided p{atom}");
                self.model_insert(atom as i64, None);
                Some(atom as i64)
            } else {
                println!("decided ¬p{atom}");
                self.model_insert(-(atom as i64), None);
                Some(-(atom as i64))
            }
        } else {
            None
        }
    }

    fn debug_decide(&mut self) -> Option<i64> {
        let at: Option<i64> = self.debug_decisions.pop();
        self.decision_level += 1;
        if let Some(atom) = at {
            let polarity: bool = get_sign(atom);
            self.unassigned.remove(&(atom.unsigned_abs() as usize));
            if polarity {
                //println!("decided p{atom}");
                self.model_insert(atom, None);
                Some(atom)
            } else {
                //println!("decided ¬p{atom}");
                self.model_insert(atom, None);
                Some(atom)
            }
        } else {
            None
        }
    }

    pub fn print_occur(&self) {
        for (i, pos) in self.occur_lists.positive.iter().enumerate().skip(1) {
            let v: Vec<usize> = pos.to_vec();
            eprintln!("p{:?}: {:?}", i, v);
        }
        for (i, neg) in self.occur_lists.negative.iter().enumerate().skip(1) {
            let v: Vec<usize> = neg.to_vec();
            eprintln!("¬p{:?}: {:?}", i, v);
        }
    }

    pub fn print_clauses(&self) {
        println!("Clauses");
        for (i, c) in self.clauses_list.iter().enumerate() {
            println!("{:?}: {:?}", i, &c.data);
        }
    }

    pub fn yield_model(&self) -> CdclResult {
        println!("Model to yield:");
        print_model(&self.model);
        let vanilla_assignment = Assignment {
            polarity: false,
            antecedent: None,
            dl: 0,
        };
        CdclResult::SAT(
            self.model
                .iter()
                .skip(1)
                .map(|k| k.unwrap_or(vanilla_assignment).polarity)
                .collect(),
        )
    }

    //Qualquer adição ao modelo deve usar essa função ou a homônima pois o tipo do modelo pode ser refatorado
    //ela checa se há contradição ou se um literal inválido está sendo adicionado
    fn model_insert(&mut self, lit: i64, antecedent: Option<usize>) -> bool {
        let atom = lit.unsigned_abs() as usize;
        match &self.model[atom] {
            Some(asgnmt) => {
                if asgnmt.polarity != get_sign(lit) {
                    return false;
                }
            }
            None => {
                self.model[atom] = Some(Assignment::new(
                    get_sign(lit),
                    self.decision_level,
                    antecedent,
                ));
            }
        }
        true
    }

    //Qualquer adição ao modelo deve usar essa função ou a homônima pois o tipo do modelo pode ser refatorado
    //ela checa se há contradição ou se um literal inválido está sendo adicionado
    fn model_insert_static(
        model: &mut [Option<Assignment>],
        lit: i64,
        antecedent: Option<usize>,
        decision_level: usize,
    ) -> bool {
        let atom = lit.unsigned_abs() as usize;
        match &model[atom] {
            Some(asgnmt) => {
                if asgnmt.polarity != get_sign(lit) {
                    return false;
                }
            }
            None => {
                model[atom] = Some(Assignment::new(get_sign(lit), decision_level, antecedent));
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_cnf_is_sat() {
        let result = run_cdcl(vec![], 0);
        assert_eq!(result, SAT(vec![]));
    }

    #[test]
    fn single_cnf_is_sat() {
        let cnf = vec![vec![1]];
        let result = run_cdcl(cnf, 1);
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
        let cnf = vec![vec![1, 2], vec![-1, -2]];
        let result = run_cdcl(cnf, 2);
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
        let cnf = vec![vec![1, 2], vec![-1, -2], vec![1, -2], vec![-1, 2]];
        let result = run_cdcl(cnf, 2);
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

    #[test]
    fn backtrack_small_case() {
        let cnf = vec![
            vec![1, -2, -6],
            vec![2, -3, 5, -1, -6],
            vec![-5, 4, 2],
            vec![1, 2],
            vec![-6, -1, 3],
            vec![6, 2, 4],
        ];

        let result = run_cdcl_debug(cnf, 6);
        match result {
            UNSAT => panic!("Expected SAT"),
            SAT(m) => println!("TODO"),
        }
    }
}

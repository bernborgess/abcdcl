use assignment::Assignment;
use clause::{Clause, Watcher::*};
use literal::Literal;
use mockall::predicate::*;
use mockall::*;
use occurlist::OccurLists;
use rand::prelude::IteratorRandom;
use rand::Rng;
use std::cmp::Ordering;
use std::collections::{HashSet, VecDeque};
use std::mem;
use utils::{print_model, remove_clauses_from_lit};
pub mod assignment;
pub mod clause;
pub mod literal;
pub mod occurlist;
pub mod utils;

type Queue = VecDeque<Literal>;

#[automock]
pub trait DecideHeuristic {
    // Gets a random boolean
    fn next_polarity(&self) -> bool;
    // Gets a random variable, if any exist
    fn next_variable(&self, unassigned: &HashSet<usize>) -> Option<usize>;
}

pub struct RandomDecideHeuristic {}

impl DecideHeuristic for RandomDecideHeuristic {
    fn next_polarity(&self) -> bool {
        let mut rng = rand::thread_rng();
        rng.gen()
    }

    fn next_variable(&self, unassigned: &HashSet<usize>) -> Option<usize> {
        let mut rng = rand::thread_rng();
        Some(*unassigned.iter().choose(&mut rng)?)
    }
}

pub fn run_cdcl(
    cnf: Vec<Vec<i64>>,
    number_of_atoms: usize,
    pre_process_switch: bool,
) -> CdclResult {
    let mut solver = Cdcl::new(number_of_atoms, RandomDecideHeuristic {}); // Uses rust RNG
    solver.solve(cnf, pre_process_switch)
}

#[derive(Clone, Debug)]
enum Seen {
    Unseen,
    Positive,
    Negative,
    Both,
}

#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}
use CdclResult::*;

pub struct Cdcl<H: DecideHeuristic> {
    pub clauses_list: Vec<Clause>,  // array de cláusulas
    unassigned: HashSet<usize>,     // conjunto de todos os átomos sem valor atribuído
    number_of_atoms: usize,         // total de átomos
    pub decision_level: usize,      // maior nível de decisão do estado
    conflicting: Option<Clause>,    // cláusula conflitante
    occur_lists: OccurLists,        //lista de ocorrências
    model: Vec<Option<Assignment>>, //elemento k é Some(true) se o átomo k for verdadeiro, Some(false) se for falso e None se não estiver atribuído
    decide_heuristic: H,
}

impl<H: DecideHeuristic> Cdcl<H> {
    #[must_use]
    pub fn new(number_of_atoms: usize, decide_heuristic: H) -> Self {
        Cdcl {
            clauses_list: vec![],
            unassigned: (1..=number_of_atoms).collect(),
            number_of_atoms,
            decision_level: 0,
            conflicting: None,
            occur_lists: OccurLists::new(0),
            model: vec![None; number_of_atoms + 1], //aloco 1 espaço a mais para garantir indexação em base 1
            decide_heuristic,
        }
    }

    pub fn solve(&mut self, cnf: Vec<Vec<i64>>, pre_process_switch: bool) -> CdclResult {
        let mut to_propagate: Option<Queue> = if pre_process_switch {
            self.pre_process(cnf) //aplica a regra PURE e outros truques de pré-processamento
        } else {
            self.clauses_list = Clause::new_vec(cnf);
            None
        };
        println!("Pre-processamento concluído: {:?}", &to_propagate);
        self.print_clauses();
        if self.clauses_list.is_empty() {
            return self.yield_model();
        }
        self.build_occur_lists();
        loop {
            while self.propagate_gives_conflict(&mut to_propagate) {
                match self.analyze_conflict() {
                    None => return UNSAT,
                    Some((b, learnt_clause)) => {
                        to_propagate = Some(self.backjump(b, learnt_clause));
                        /*// Add learnt clause to clause list
                        self.add_clause(learnt_clause.literals.clone());
                        // Apply backtrack of dl b
                        self.backtrack(b);
                        // Set new dl to b
                        self.decision_level = b;
                        // Add negation of the unset literal in learnt_clause to the model
                        let unset_literal = learnt_clause
                            .literals
                            .iter()
                            .find(|lit| self.model[lit.variable].is_none())
                            .cloned()
                            .expect("No unset literal was found!");

                        let learned_literal = unset_literal.negate();
                        let antecedent_id = self.clauses_list.len() - 1;
                        self.model_insert(learned_literal, Some(antecedent_id));

                        // Add it to propagate too
                        to_propagate
                            .get_or_insert_with(VecDeque::new)
                            .push_back(learned_literal);*/
                    }
                }
            }
            //restart_if_applicable();
            //remove_lemmas_if_applicable();
            match self.decide() {
                None => return self.yield_model(),
                Some(a) => to_propagate = Some(VecDeque::from(vec![a])),
            }
        }
    }

    // Remove duplicatas, realiza atribuições triviais (PURE e cláusulas unitárias), remove cláusulas satisfeitas
    // retorna vetor de Literal para propagar e constrói as cláusulas do solver
    pub fn pre_process(&mut self, mut cnf: Vec<Vec<i64>>) -> Option<Queue> {
        let mut decided: Queue = VecDeque::new();
        let mut clauses_to_remove: HashSet<usize> = HashSet::new();
        let mut seen_status: Vec<Seen> = vec![Seen::Unseen; self.number_of_atoms + 1]; // 1 campo extra para indexar em base 1
        let mut full_occur_lists = OccurLists::new(self.number_of_atoms + 1); // 1 campo extra para indexar em base 1
        for (clause_ind, clause) in cnf.iter_mut().enumerate() {
            if clause.len() == 1 {
                // se essa cláusula só tem um literal, então só atribuições que tornam esse literal verdadeiro podem ser modelos
                let lit = Literal::new(&clause[0]);
                decided.push_back(lit);
                clauses_to_remove.insert(clause_ind);
            }
            // Vou supor que não vão existir cláusulas triviais (ex: 1 -1 2 -4 0) em nossos casos de teste pelo bem da minha sanidade
            for &raw_lit in clause.iter() {
                let lit = Literal::new(&raw_lit);
                let full_list = full_occur_lists.get_mut(lit);
                match raw_lit.cmp(&0) {
                    Ordering::Less => {
                        full_list.push(clause_ind);
                        seen_status[lit.variable] = match seen_status[lit.variable] {
                            Seen::Unseen => Seen::Negative,
                            Seen::Positive => Seen::Both,
                            Seen::Negative => Seen::Negative,
                            Seen::Both => Seen::Both,
                        };
                    }
                    Ordering::Greater => {
                        full_list.push(clause_ind);
                        seen_status[lit.variable] = match seen_status[lit.variable] {
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
            let lit = Literal::new(&(index as i64));
            //check
            match status {
                Seen::Unseen => decided.push_back(lit), // se o átomo não aparece na fórmula posso atribuir o valor que eu quiser
                Seen::Positive => decided.push_back(lit),
                Seen::Negative => decided.push_back(lit.negate()),
                Seen::Both => {}
            }
        }

        self.grow_model_and_remove_clauses(&decided, &mut clauses_to_remove, &full_occur_lists, cnf)
            .map(|filtered_cnf| {
                self.clauses_list = Clause::new_vec(filtered_cnf);
                decided
            })
    }

    pub fn build_occur_lists(&mut self) {
        let mut occur_lists = OccurLists::new(self.number_of_atoms);
        for (c_ind, c) in self.clauses_list.iter().enumerate() {
            for &lit in c.literals.iter().take(2) {
                occur_lists.add_clause_to_lit(c_ind, lit);
            }
        }
        self.occur_lists = occur_lists;
    }

    fn grow_model_and_remove_clauses(
        &mut self,
        decided: &Queue,
        clauses_to_remove: &mut HashSet<usize>,
        full_occur_lists: &OccurLists,
        mut cnf: Vec<Vec<i64>>,
    ) -> Option<Vec<Vec<i64>>> {
        for &lit in decided.iter() {
            if !self.model_insert(lit, None) {
                return None; //Unsat case
            }
            self.unassigned.remove(&lit.variable);
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

    pub fn propagate_gives_conflict(&mut self, to_propagate: &mut Option<Queue>) -> bool {
        //arranco o modelo do solver para resolver conflitos com o borrow checker
        let mut model: Vec<Option<Assignment>> = mem::take(&mut self.model);
        let occur_lists: &mut OccurLists = &mut self.occur_lists;
        let to_propagate: Option<Queue> = to_propagate.take();
        //println!("trivial_or_decided: {:?}", &trivial_or_decided);
        let mut to_propagate: Queue = to_propagate.unwrap_or_default();
        loop {
            //print_model(&model);
            match to_propagate.pop_front() {
                None => {
                    //a fila está vazia, não tem nada para propagar, então retorno sem acusar conflito
                    self.model = model;
                    return false;
                }
                Some(current) => {
                    let mut clauses_to_watch: Vec<usize> = occur_lists.take(current.negate());
                    /*println!(
                        "occur_list[{:?}] = {:?}",
                        current.negate(),
                        &clauses_to_watch
                    );*/
                    let mut to_remove_from_occur: Vec<usize> = vec![];
                    for &c_ind in clauses_to_watch.iter() {
                        //println!("Clause {c_ind}:{:?}", self.clauses_list[c_ind]);
                        match self.clauses_list[c_ind].watch(
                            current.negate(),
                            &model,
                            self.decision_level,
                        ) {
                            // não encontrou unidade
                            Watched(new_watched) => {
                                // Adiciona a cláusula atual a lista de ocorrências do novo literal vigiado
                                occur_lists.add_clause_to_lit(c_ind, new_watched);
                                to_remove_from_occur.push(c_ind);
                            }
                            OnlyOneRemaining(to_prop) => {
                                // checa se to_prop é conflitante com o modelo
                                match Cdcl::<H>::model_opinion(&model, to_prop) {
                                    Some(false) => {
                                        // absoluto vivo código
                                        // last standing é falseado pelo modelo e falseado pelo modelo, então um conflito foi encontrado
                                        self.conflicting = Some(self.clauses_list[c_ind].clone());
                                        self.model = model;
                                        occur_lists.give_to(clauses_to_watch, current.negate());
                                        return true;
                                    }
                                    Some(true) => {
                                        self.clauses_list[c_ind].set_satisfied(self.decision_level);
                                        to_remove_from_occur.push(c_ind); // ???? checking
                                    }
                                    None => {
                                        self.unassigned.remove(&to_prop.variable);
                                        to_propagate.push_back(to_prop);
                                        Cdcl::<H>::model_insert_static(
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
                            AlreadyWatched => (),
                        }
                    }
                    // Atualiza a lista de ocorrência que foi iterada recentemente para retirar as cláusulas que não são mais vigiadas
                    remove_clauses_from_lit(&to_remove_from_occur, &mut clauses_to_watch);
                    occur_lists.give_to(clauses_to_watch, current.negate());
                }
            };
        }
    }

    fn model_opinion(model: &[Option<Assignment>], lit: Literal) -> Option<bool> {
        model[lit.variable].map(|b| b.polarity == lit.polarity)
    }

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
        let mut literals: Queue = learnt
            .literals
            .iter()
            .filter(|lit| self.literal_has_max_dl(**lit))
            .copied()
            .collect();

        while literals.len() != 1 {
            // Implied literals
            literals.retain(|lit| {
                self.model[lit.variable]
                    .expect("Conflict should be assigned for all variables")
                    .antecedent
                    .is_some()
            });
            // Select any literal that meets the criterion
            let literal = literals.front();
            if literal.is_none() {
                break;
            }
            let literal = *literal.unwrap();
            let antecedent = &self.get_antecedent(literal);
            if antecedent.is_none() {
                break;
            }
            let antecedent = &self.clauses_list[antecedent.unwrap()];
            learnt = learnt.resolution(antecedent, literal);
            // Literals with current decision level
            literals = learnt
                .literals
                .iter()
                .filter(|lit| self.literal_has_max_dl(**lit))
                .copied()
                .collect();
        }

        // out of the loop, `learnt` is now the new clause
        // compute the backtrack level b (second largest decision level)
        let mut b = 0;
        for lit in &learnt.literals {
            if self.literal_has_max_dl(*lit) {
                continue;
            }
            b = std::cmp::max(b, self.literal_get_dl(*lit));
        }
        Some((b, learnt))
    }

    /// Returns index of clause that propagated this literal
    fn get_antecedent(&self, lit: Literal) -> Option<usize> {
        self.model[lit.variable]?.antecedent
    }

    /// Add a new clause and prepares the watched literals
    fn add_clause(&mut self, literals: Vec<Literal>) {
        let new_clause_id = self.clauses_list.len();

        if self.clauses_list.len() < 2 {
            return;
        }

        // Update occurlist
        let lit1 = literals[0];
        let lit2 = literals[1];

        self.occur_lists.add_clause_to_lit(new_clause_id, lit1);
        self.occur_lists.add_clause_to_lit(new_clause_id, lit2);

        // Add clause to problem
        let learnt_clause = Clause::new(literals);
        self.clauses_list.push(learnt_clause);
    }

    //muda para None a atribuição de variáveis com decision level maior que b
    //retorna a fila de literais que devem propagados para concluir o literal de maior decision level na cláusula aprendida
    fn backjump(&mut self, b: usize, learnt_clause: Clause) -> Queue {
        // Coloca as negações de todos os literais de dl mais baixo em uma fila para
        // serem propagados e deduzirem o literal de maior dl na cláusula aprendida
        let mut to_propagate: Queue = Queue::new();
        for &lit in learnt_clause.literals.iter() {
            if !self.literal_has_max_dl(lit) {
                to_propagate.push_front(lit.negate());
            }
        }
        //adiciona a cláusula aprendida ao solver
        self.add_clause(learnt_clause.literals);

        // Remove todos as atribuições com dl maior que b do modelo
        for asg in self.model.iter_mut().skip(1) {
            if let Some(asgnmt) = asg {
                if asgnmt.dl > b {
                    *asg = None;
                }
            }
        }

        // Torna b o decision level atual
        self.decision_level = b;

        // Limpa o campo de cláusula de conflito
        self.conflicting = None;

        to_propagate
    }

    fn literal_is_undefined(&self, lit: Literal) -> bool {
        self.model[lit.variable].is_none()
    }

    fn literal_get_dl(&self, lit: Literal) -> usize {
        if let Some(ass) = self.model[lit.variable] {
            ass.dl
        } else {
            0
        }
    }

    fn literal_has_dl(&self, lit: Literal, dl: usize) -> bool {
        if self.literal_is_undefined(lit) {
            return false;
        }
        let actual_dl = self.literal_get_dl(lit);
        actual_dl == dl
    }

    fn literal_has_max_dl(&self, lit: Literal) -> bool {
        self.literal_has_dl(lit, self.decision_level)
    }

    fn _restart_if_applicable(&self) {
        eprintln!("TODO: restart_if_applicable");
    }

    fn _remove_lemmas_if_applicable(&self) {
        eprintln!("TODO: remove_lemmas_if_applicable");
    }

    fn decide(&mut self) -> Option<Literal> {
        //print_model(&self.model);
        let polarity = self.decide_heuristic.next_polarity();
        let variable = self.decide_heuristic.next_variable(&self.unassigned)?;
        self.decision_level += 1;
        self.unassigned.remove(&variable);
        let lit: Literal = Literal { variable, polarity };
        //eprintln!("decided {lit}");
        self.model_insert(lit, None);
        Some(lit)
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
            println!("{:?}: {:?}", i, &c.literals);
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
    fn model_insert(&mut self, lit: Literal, antecedent: Option<usize>) -> bool {
        match &self.model[lit.variable] {
            Some(ass) => {
                if ass.polarity != lit.polarity {
                    return false;
                }
            }
            None => {
                self.model[lit.variable] = Some(Assignment::new(
                    lit.polarity,
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
        lit: Literal,
        antecedent: Option<usize>,
        decision_level: usize,
    ) -> bool {
        match &model[lit.variable] {
            Some(ass) => {
                if ass.polarity != lit.polarity {
                    return false;
                }
            }
            None => {
                model[lit.variable] =
                    Some(Assignment::new(lit.polarity, decision_level, antecedent));
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use rand::rngs::mock;

    use super::*;

    #[cfg(test)]
    fn setup_mock(polarities: Vec<bool>, variables: Vec<usize>) -> MockDecideHeuristic {
        let mut mock_decide_heuristic = MockDecideHeuristic::new();

        // Setup answers for `next_polarity()`
        let mut sequence = Sequence::new();
        for pol in polarities {
            mock_decide_heuristic
                .expect_next_polarity()
                .times(1)
                .in_sequence(&mut sequence)
                .return_const(pol);
        }

        mock_decide_heuristic
            .expect_next_polarity()
            .returning(|| rand::random::<bool>());

        // Setup answers for `next_variable()`
        let mut sequence = Sequence::new();
        for var in variables {
            mock_decide_heuristic
                .expect_next_variable()
                .times(1)
                .in_sequence(&mut sequence)
                .return_const(var);
        }

        // Return a random variable from the unassigned set when expectations are exhausted
        mock_decide_heuristic
            .expect_next_variable()
            .returning(|unassigned| {
                let mut rng = rand::thread_rng(); // Create RNG inside the closure
                unassigned.iter().copied().choose(&mut rng)
            });

        mock_decide_heuristic
    }

    #[test]
    fn empty_cnf_is_sat() {
        let result = run_cdcl(vec![], 0, true);
        assert_eq!(result, SAT(vec![]));
    }

    #[test]
    fn single_cnf_is_sat() {
        let cnf = vec![vec![1]];
        let result = run_cdcl(cnf, 1, true);
        match result {
            SAT(assign) => {
                assert_eq!(assign.len(), 1);
                assert!(assign[0]);
            }
            _ => panic!("single cnf is sat"),
        }
    }

    #[test]
    fn two_cnf_is_sat() {
        let cnf = vec![vec![1, 2], vec![-1, -2]];
        let result = run_cdcl(cnf, 2, true);
        match result {
            SAT(assign) => {
                assert_eq!(assign.len(), 2);
                // Either [T,F] or [F,T]
                assert!(assign == vec![true, false] || assign == vec![false, true]);
            }
            _ => panic!("two cnf is sat fail"),
        }
    }

    #[test]
    fn two_cnf_is_unsat() {
        let cnf = vec![vec![1, 2], vec![-1, -2], vec![1, -2], vec![-1, 2]];
        // TODO: Fix the backtrack to call this test...
        let result = run_cdcl(cnf, 2, true);
        //let result = UNSAT;
        match result {
            UNSAT => (),
            _ => panic!("two cnf is unsat fail"),
        }
    }

    #[test]
    fn pre_process_can_solve() {
        let decide_heuristic = RandomDecideHeuristic {};
        let mut solver = Cdcl::new(6, decide_heuristic);
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
        solver.pre_process(original_cnf);
        assert_eq!(0, solver.clauses_list.len())
    }

    #[test]
    fn pre_process_worked() {
        let mock_decide_heuristic = MockDecideHeuristic::new();

        let mut solver = Cdcl::new(7, mock_decide_heuristic);
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
            for (j, &lit) in c.literals.iter().enumerate() {
                assert_eq!(lit, Literal::new(&target_cnf[i][j]));
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

        let polarities = vec![false, true];
        let variables = vec![2, 6];
        let mock_decide_heuristic = setup_mock(polarities, variables);

        let mut solver = Cdcl::new(6, mock_decide_heuristic);
        let result = solver.solve(cnf, false);
        match result {
            SAT(model) => assert_eq!(model, vec![true, false, true, false, false, true]),
            UNSAT => panic!("backtrack small case fail"),
        }
    }

    #[test]
    fn check_return_level() {
        let cnf = vec![
            vec![-2, -3, -4],
            vec![-3, -5, -6],
            vec![4, 6, 7],
            vec![-7, -8],
            vec![-1, -7, -9],
            vec![-1, 8, 9],
        ];

        let polarities = vec![true, true, true, true];
        let variables = vec![5, 3, 2, 1];
        let mock_decide_heuristic = setup_mock(polarities, variables);

        let mut solver = Cdcl::new(9, mock_decide_heuristic);
        let result = solver.solve(cnf, false);
        // TODO: How to get what "Mock(b)" was returning??
        match result {
            UNSAT => println!("We got unsat..."),
            SAT(model) => println!("We got sat...{}", model.len()),
        }
    }
}

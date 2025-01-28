use assignment::Assignment;
use clause::Clause;
use literal::Literal;
use mockall::predicate::*;
use mockall::*;
use rand::prelude::IteratorRandom;
use rand::Rng;
use std::cmp::{max, min, Reverse};
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;
use CdclResult::*;
pub mod assignment;
pub mod clause;
pub mod literal;
pub mod occurlist;
pub mod utils;

type Queue = VecDeque<Literal>;
type ClauseIndex = usize;

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

pub fn run_cdcl(cnf: Vec<Vec<i64>>, number_of_atoms: usize) -> CdclResult {
    let mut solver = Cdcl::new(cnf, number_of_atoms, RandomDecideHeuristic {}); // Uses rust RNG
    solver.solve()
}

#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}

impl fmt::Display for CdclResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CdclResult::UNSAT => write!(f, "Unsatisfiable formula"),
            CdclResult::SAT(ref msg) => write!(f, "Model: {:?}", msg),
        }
    }
}

pub struct Cdcl<H: DecideHeuristic> {
    pub formula: Vec<Clause>,
    pub decision_level: usize,
    model: Vec<Option<Assignment>>,
    clauses_with_lit_watched: HashMap<Literal, HashSet<ClauseIndex>>,
    decide_heuristic: H,
}

enum UnitPropagationResult {
    Unresolved,
    Conflict(ClauseIndex),
}

fn resolve(clause_a: &Clause, clause_b: &Clause, pivot: Literal) -> Clause {
    // TODO
    Clause::new(vec![])
}

impl<H: DecideHeuristic> Cdcl<H> {
    #[must_use]
    pub fn new(raw_cnf: Vec<Vec<i64>>, number_of_atoms: usize, decide_heuristic: H) -> Self {
        // TODO: Pre processing to get rid of trivial clauses

        Cdcl {
            formula: Clause::new_vec(raw_cnf),
            decision_level: 0,
            model: vec![None; number_of_atoms + 1],
            clauses_with_lit_watched: HashMap::new(),
            decide_heuristic,
        }
    }

    pub fn solve(&mut self) -> CdclResult {
        // Primeiramente obtemos a `formula` e inicializamos os `watch_pointers` e
        // `clauses_with_lit_watched` com os primeiros dois literais de cada clausula
        self.init_watches();

        // Para cada clausula com um único literal, adicionamos a negação deste a fila
        // `to_propagate`, caso esta variável ja nao ocorra no `model`
        let mut to_propagate: Queue = VecDeque::new();
        for clause_index in 0..self.formula.len() {
            let clause = &self.formula[clause_index];
            if clause.literals.len() != 1 {
                continue;
            }
            let lit = clause.literals[0];
            if self.model[lit.variable].is_none() {
                // Adicionamos ao model
                self.model[lit.variable] =
                    Some(Assignment::new(lit.polarity, 0, Some(clause_index)));
                // Sua negação eh propagada
                to_propagate.push_back(lit.negate());
            }
        }

        // Invocamos o método `unit_propagation` e notamos o resultado
        // Se reason for "conflict", temos uma contradição, retornamos UNSAT.
        if let UnitPropagationResult::Conflict(_) = self.unit_propagation(&mut to_propagate) {
            return UNSAT;
        }

        // Enquanto nao tivermos uma valoração em `model` para todas as variáveis de `formula`
        while !self.all_variables_assigned() {
            // Invocamos o método `decide`, obtendo um literal
            let lit = self.decide();

            // Incrementamos o `decision_level`
            self.decision_level += 1;

            // Adicionamos `lit` ao `model`
            self.model_assign(lit, None);

            // Atribuímos a negação de `lit` para a fila `to_propagate`
            to_propagate.clear();
            to_propagate.push_back(lit.negate());

            loop {
                // Invocamos `unit_propagation`
                match self.unit_propagation(&mut to_propagate) {
                    // Se `reason` nao for "conflict", saímos do loop para decidir novamente
                    UnitPropagationResult::Unresolved => break,
                    UnitPropagationResult::Conflict(conflict_clause_index) => {
                        // Invocamos `conflict_analysis` obtendo `b` e `learnt_clause`
                        match self.conflict_analysis(conflict_clause_index) {
                            // se falhar retornamos UNSAT
                            None => return UNSAT,
                            Some((b, learnt_clause)) => {
                                // Invocamos `add_learnt_clause` e `backtrack`
                                let learnt_clause_index = self.add_learnt_clause(&learnt_clause);
                                self.backtrack(b, learnt_clause_index);
                                // Atribuímos `b` como novo decision level
                                self.decision_level = b;

                                // Nesse momento ha apenas um literal `lit` em `learnt_clause`
                                // e nao no `model`
                                let lit: Literal = learnt_clause
                                    .literals
                                    .iter()
                                    .find(|lit| self.model[lit.variable].is_none())
                                    .cloned()
                                    .expect("No literal was learned");

                                // Adicionamos a negação de `lit` ao `model`, com antecedente `learnt_clause`
                                self.model_assign(lit.negate(), Some(learnt_clause_index));

                                // `to_propagate` sera agora apenas `lit`
                                to_propagate.clear();
                                to_propagate.push_back(lit);
                            }
                        }
                    }
                }
            }
        }
        self.yield_model()
    }

    /// Inicializamos os `watch_pointers` e `clauses_with_lit_watched`
    /// com os primeiros dois literais de cada clausula
    fn init_watches(&mut self) {
        for (clause_index, clause) in self.formula.iter().enumerate() {
            for lit_index in 0..(min(clause.literals.len(), 2)) {
                let lit = clause.literals[lit_index];
                // Adicione o índice da clausula ao conjunto de
                // clausulas observadas por este literal
                self.clauses_with_lit_watched
                    .entry(lit)
                    .or_default()
                    .insert(clause_index);
            }
        }
    }

    fn unit_propagation(&mut self, to_propagate: &mut Queue) -> UnitPropagationResult {
        // Enquanto ha literais para propagar tomamos `watching_lit`
        while let Some(watching_lit) = to_propagate.pop_front() {
            // Para cada `clause` em que `watching_lit` ocorre,
            if let Some(clause_indices) = self.clauses_with_lit_watched.get(&watching_lit).cloned()
            {
                let mut rewatched = false;
                for watching_clause_index in clause_indices {
                    let watching_clause = &mut self.formula[watching_clause_index];
                    let mut watched_lits = vec![];
                    for wp_index in watching_clause.watch_pointers {
                        watched_lits.push(watching_clause.literals[wp_index]);
                    }

                    // Para cada literal nessa `clause`
                    for (lit_index, &lit) in watching_clause.literals.iter().enumerate() {
                        if watched_lits.contains(&lit) {
                            continue;
                        }
                        if let Some(asgnmt) = self.model[lit.variable] {
                            if !asgnmt.polarity {
                                continue;
                            }
                        }
                        // Se encontramos um `lit` nao observado e nao valorado como F no model
                        // Começamos a observar `lit`, em vez de `watching_lit`
                        let idx = if watching_clause.literals[watching_clause.watch_pointers[0]]
                            == watching_lit
                        {
                            0
                        } else {
                            1
                        }; // TODO: Readability
                        watching_clause.watch_pointers[idx] = lit_index;

                        self.clauses_with_lit_watched
                            .entry(watching_lit)
                            .or_default()
                            .remove(&watching_clause_index);

                        self.clauses_with_lit_watched
                            .entry(lit)
                            .or_default()
                            .insert(watching_clause_index);

                        rewatched = true;
                    }
                    if !rewatched {
                        // Se ha apenas um literal observado em `watching_clause`
                        if watching_clause.watch_pointers[0] == watching_clause.watch_pointers[1] {
                            // retornamos um conflito
                            return UnitPropagationResult::Conflict(watching_clause_index);
                        }
                        // Caso contrario tomamos `other` o outro literal observado.
                        let other: Literal = if watching_lit
                            == watching_clause.literals[watching_clause.watch_pointers[0]]
                        {
                            watching_clause.literals[watching_clause.watch_pointers[1]]
                        } else {
                            watching_clause.literals[watching_clause.watch_pointers[0]]
                        }; // TODO: readability

                        match self.model[other.variable] {
                            // Se `other` nao esta definido no model
                            None => {
                                // Adicionamos esta ao model
                                self.model_assign(other, Some(watching_clause_index));
                                // Propagamos
                                to_propagate.push_back(other);
                            }
                            Some(asgnmt) => {
                                // Se outro eh T no modelo, continuamos
                                if asgnmt.polarity {
                                    continue;
                                }
                                // Se outro eh F no modelo, temos um Conflito
                                else {
                                    return UnitPropagationResult::Conflict(watching_clause_index);
                                }
                            }
                        }
                    }
                }
            }
        }
        UnitPropagationResult::Unresolved
    }

    fn all_variables_assigned(&self) -> bool {
        for lit in &self.model {
            if lit.is_none() {
                return false;
            }
        }
        true
    }

    /// Returns what decision level needs to be decremented
    fn conflict_analysis(&self, conflict_clause_index: ClauseIndex) -> Option<(usize, Clause)> {
        if self.decision_level == 0 {
            return None;
        }

        let conflict_clause = &self.formula[conflict_clause_index];

        // Para cada `literal` da `conflict_clause`
        // Cujo decision level eh o atual
        let mut literals: Queue = conflict_clause
        .literals
        .iter()
        .filter(|lit| match self.model[lit.variable] {
            None => false,
            Some(asgnmt) => asgnmt.dl == self.decision_level /*&& asgnmt.antecedent.is_some()*/,
        })
        .copied()
        .collect();

        let mut learnt_clause = conflict_clause.clone();

        while literals.len() != 1 {
            // E o antecedente existe i.e. ele foi propagado
            literals.retain(|lit| {
                self.model[lit.variable]
                    .expect("Conflict should be assigned for all variables")
                    .antecedent
                    .is_some()
            });
            let literal = literals.front();
            if literal.is_none() {
                break;
            }
            let literal = *literal.unwrap();

            // Tomamos o seu `antecedent` i.e. os literais da clausula unitária que propagou esse literal
            let antecedent = &self.model[literal.variable]?.antecedent;
            if antecedent.is_none() {
                break;
            }
            let antecedent = &self.formula[antecedent.unwrap()];

            // Calculamos a `resolution` de `learnt_clause` e `antecedent` com pivô `literal`
            // A clausula resolvida eh a nova clausula conflitante, chamada "aprendida"
            learnt_clause = resolve(&learnt_clause, antecedent, literal);
        }

        // Temos uma clausula aprendida `learnt_clause`
        // Analisamos o decision level dos literais contidos nessa clausula

        // Se forem todos iguais, retornamos b = 0 e learnt_clause
        // Caso contrario, calculamos b para o (segundo) maior decision level em aprendida
        let mut b = 0;
        for lit in &learnt_clause.literals {
            match self.model[lit.variable] {
                None => continue,
                Some(asgnmt) => {
                    if asgnmt.dl < self.decision_level {
                        // Armazena o maior decision level encontrado,
                        // quando menor que o `self.decision_level`
                        b = max(b, asgnmt.dl);
                    }
                }
            }
        }
        Some((b, learnt_clause))
    }

    /// Add a new clause and prepares the watched literals
    /// Returns the index of the new clause
    fn add_learnt_clause(&mut self, learnt_clause: &Clause) -> ClauseIndex {
        let new_clause_id = self.formula.len();
        // Adicione `learnt_clause` as clausulas da formula
        self.formula.push(learnt_clause.clone());

        // Se houver somente um literal na clausula terminamos
        if learnt_clause.literals.len() < 2 {
            let lit = learnt_clause.literals[0];
            self.clauses_with_lit_watched
                .entry(lit)
                .or_default()
                .insert(new_clause_id);
            self.formula[new_clause_id].watch_pointers[0] = 0;
            return new_clause_id;
        }

        // Atribua `watch_pointers` aos dois literais de `learnt_clause`
        // com maior decision level
        let mut heap_of_two = BinaryHeap::with_capacity(2);
        for (literal_index, literal) in learnt_clause.literals.iter().enumerate() {
            if let Some(asgnmt) = self.model[literal.variable] {
                // Manter os dois melhores na heap
                heap_of_two.push(Reverse((asgnmt.dl, literal, literal_index)));
                while heap_of_two.len() > 2 {
                    heap_of_two.pop();
                }
            }
        }
        for (i, Reverse((_, to_watch_lit, lit_index))) in heap_of_two.into_vec().iter().enumerate()
        {
            // Atualize `clauses_with_lit_watched` com `learnt_clause` para estes literais
            self.clauses_with_lit_watched
                .entry(**to_watch_lit)
                .or_default()
                .insert(new_clause_id);
            self.formula[new_clause_id].watch_pointers[i] = *lit_index;
        }

        new_clause_id
    }

    //muda para None a atribuição de variáveis com decision level maior que b
    //retorna a fila de literais que devem propagados para concluir o literal de maior decision level na cláusula aprendida
    fn backtrack(&mut self, b: usize, learnt_clause_index: ClauseIndex) {
        for lit in &self.formula[learnt_clause_index].literals {
            if let Some(ass) = self.model[lit.variable] {
                if ass.dl <= b {
                    continue;
                }
                self.model[lit.variable] = None;
            }
        }
    }

    // Chooses a variable and a value to it
    // Panics if no variable is unassigned
    fn decide(&mut self) -> Literal {
        // TODO
        Literal {
            variable: 0,
            polarity: false,
        }
    }

    fn model_assign(&mut self, lit: Literal, antecedent: Option<ClauseIndex>) {
        // TODO
    }

    pub fn yield_model(&self) -> CdclResult {
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
}

#[cfg(test)]
mod tests {
    use crate::{cdcl::clause::Watcher, parser::read_from_string};

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
    fn contradiction_is_unsat() {
        let result = run_cdcl(vec![vec![1], vec![-1]], 3);
        assert_eq!(result, UNSAT);
    }

    #[test]
    fn empty_cnf_is_sat() {
        let result = run_cdcl(vec![], 5);
        assert_eq!(result, SAT(vec![true, true, true, true, true]));
    }

    #[test]
    fn single_cnf_is_sat() {
        let cnf = vec![vec![1]];
        let result = run_cdcl(cnf, 1);
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
        let result = run_cdcl(cnf, 2);
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
        let polarities = vec![false];
        let variables = vec![2];
        let mock_decide_heuristic = setup_mock(polarities, variables);

        let mut solver = Cdcl::new(cnf, 2, mock_decide_heuristic);
        let result = solver.solve();
        assert_eq!(result, UNSAT);
    }

    #[test]
    fn pre_process_can_solve() {
        let decide_heuristic = RandomDecideHeuristic {};
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
        let mut solver = Cdcl::new(original_cnf, 6, decide_heuristic);
        // solver.pre_process(original_cnf);
        assert_eq!(0, solver.formula.len())
    }

    #[test]
    fn pre_process_worked() {
        let mock_decide_heuristic = MockDecideHeuristic::new();

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
        let mut solver = Cdcl::new(original_cnf, 7, mock_decide_heuristic);
        let target_cnf: Vec<Vec<i64>> = vec![
            //must remove clauses with 1 (verified by unit clause) or -2 (verified by pure)
            vec![-7, 6],
            vec![5, 7],
            vec![-1, 4, 5],
            vec![-6, -4, -3],
            vec![-5, -3, 4],
        ];

        // let _ = solver.pre_process(original_cnf);

        for (i, c) in solver.formula.iter().enumerate() {
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

        let mut solver = Cdcl::new(cnf, 6, mock_decide_heuristic);
        let result = solver.solve();
        match result {
            SAT(model) => assert_eq!(model, vec![true, false, true, true, true, true]),
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
        let mut solver = Cdcl::new(cnf, 9, mock_decide_heuristic);
        let result = solver.solve();
        // TODO: How to get what "Mock(b)" was returning??
        match result {
            UNSAT => println!("We got unsat..."),
            SAT(model) => println!("We got sat...{:?}", model),
        }
    }

    #[test]
    fn check_dubois20() {
        let (cnf, lits) = read_from_string("./test/dubois20.cnf");
        let result = run_cdcl(cnf, lits);
        match result {
            CdclResult::SAT(_) => println!("\nSAT"),
            CdclResult::UNSAT => println!("\nUNSAT"),
        }
    }

    #[test]
    fn watch_case1() {
        //lit_watch_pointer=other_watch_pointer+1
        //ans before
        let literals: Vec<Literal> = vec![
            //Literal::new(&1),
            Literal::new(&2),
            Literal::new(&3),
            Literal::new(&4),
            Literal::new(&5),
            /*Literal::new(&53),
            Literal::new(&15),
            Literal::new(&17),*/
        ];
        let mut clause: Clause = Clause::new(literals);
        clause.watch_pointers[0] = 2; //other watch pointer
        clause.watch_pointers[1] = 3; //lit watch pointer
        let mut model: Vec<Option<Assignment>> = vec![None; 54];
        let opt_asgnmt_f: Option<Assignment> = Some(Assignment {
            polarity: false,
            dl: 0,
            antecedent: None,
        });
        let opt_asgnmt_t: Option<Assignment> = Some(Assignment {
            polarity: true,
            dl: 0,
            antecedent: None,
        });
        model[1] = opt_asgnmt_f;
        model[2] = opt_asgnmt_f;
        model[3] = opt_asgnmt_f;
        model[4] = None;
        model[5] = opt_asgnmt_f;
        model[53] = opt_asgnmt_f;
        model[15] = opt_asgnmt_f;
        model[17] = opt_asgnmt_f;
        println!("Clause: {:?}", &clause);
        let ans = clause.watch(Literal::new(&5), &model);
        println!("Clause: {:?}", &clause);
        println!("ans {:?}", &ans);
        assert_eq!(ans, Watcher::Unit(Literal::new(&4)))
    }

    #[test]
    //lit_watch_pointer=other_watch_pointer+n
    //n>1; result before other_watch_pointer
    fn watch_case2() {
        let literals: Vec<Literal> = vec![
            Literal::new(&1),
            Literal::new(&2),
            Literal::new(&3),
            Literal::new(&4),
            Literal::new(&5),
            Literal::new(&53),
            Literal::new(&15),
            Literal::new(&17),
        ];
        let mut clause: Clause = Clause::new(literals);
        clause.watch_pointers[0] = 3; //other watch pointer
        clause.watch_pointers[1] = 5; //lit watch pointer
        let mut model: Vec<Option<Assignment>> = vec![None; 54];
        let opt_asgnmt_f: Option<Assignment> = Some(Assignment {
            polarity: false,
            dl: 0,
            antecedent: None,
        });
        let opt_asgnmt_t: Option<Assignment> = Some(Assignment {
            polarity: true,
            dl: 0,
            antecedent: None,
        });
        model[1] = opt_asgnmt_f;
        model[2] = opt_asgnmt_f;
        model[3] = opt_asgnmt_t;
        model[4] = opt_asgnmt_f;
        model[5] = opt_asgnmt_f;
        model[53] = opt_asgnmt_f;
        model[15] = opt_asgnmt_f;
        model[17] = opt_asgnmt_f;
        println!("Clause: {:?}", &clause);
        let ans = clause.watch(Literal::new(&53), &model);
        println!("Clause: {:?}", &clause);
        println!("ans {:?}", &ans);
        assert_eq!(ans, Watcher::Satisfied(Literal::new(&3)))
    }

    #[test]
    //lit_watch_pointer=other_watch_pointer+n
    //n>1; result between pointers
    fn watch_case3() {
        let literals: Vec<Literal> = vec![
            //Literal::new(&1),
            //Literal::new(&2),
            Literal::new(&3),
            Literal::new(&4),
            Literal::new(&5),
            Literal::new(&53),
            //Literal::new(&15),
            //Literal::new(&17),
        ];
        let mut clause: Clause = Clause::new(literals);
        clause.watch_pointers[0] = 1; //other watch pointer
        clause.watch_pointers[1] = 3; //lit watch pointer
        let mut model: Vec<Option<Assignment>> = vec![None; 54];
        let opt_asgnmt_f: Option<Assignment> = Some(Assignment {
            polarity: false,
            dl: 0,
            antecedent: None,
        });
        let opt_asgnmt_t: Option<Assignment> = Some(Assignment {
            polarity: true,
            dl: 0,
            antecedent: None,
        });
        model[1] = opt_asgnmt_f;
        model[2] = opt_asgnmt_f;
        model[3] = opt_asgnmt_f;
        model[4] = opt_asgnmt_f;
        model[5] = opt_asgnmt_t;
        model[53] = opt_asgnmt_f;
        model[15] = opt_asgnmt_f;
        model[17] = opt_asgnmt_f;
        println!("Clause: {:?}", &clause);
        let ans = clause.watch(Literal::new(&53), &model);
        println!("Clause: {:?}", &clause);
        println!("ans {:?}", &ans);
        assert_eq!(ans, Watcher::Satisfied(Literal::new(&5)))
    }

    #[test]
    fn watch_case4() {
        //lit_watch_pointer<other_watch_pointer
        //ans before
        let literals: Vec<Literal> = vec![
            //Literal::new(&1),
            Literal::new(&2),
            Literal::new(&3),
            Literal::new(&4),
            Literal::new(&5),
            Literal::new(&53),
            //Literal::new(&15),
            //Literal::new(&17),
        ];
        let mut clause: Clause = Clause::new(literals);
        clause.watch_pointers[0] = 2; //other watch pointer
        clause.watch_pointers[1] = 3; //lit watch pointer
        let mut model: Vec<Option<Assignment>> = vec![None; 54];
        let opt_asgnmt_f: Option<Assignment> = Some(Assignment {
            polarity: false,
            dl: 0,
            antecedent: None,
        });
        let opt_asgnmt_t: Option<Assignment> = Some(Assignment {
            polarity: true,
            dl: 0,
            antecedent: None,
        });
        model[1] = opt_asgnmt_f;
        model[2] = opt_asgnmt_f;
        model[3] = opt_asgnmt_t;
        model[4] = opt_asgnmt_f;
        model[5] = opt_asgnmt_f;
        model[53] = opt_asgnmt_f;
        model[15] = opt_asgnmt_f;
        model[17] = opt_asgnmt_f;
        println!("Clause: {:?}", &clause);
        let ans = clause.watch(Literal::new(&4), &model);
        println!("Clause: {:?}", &clause);
        println!("ans {:?}", &ans);
        assert_eq!(ans, Watcher::Satisfied(Literal::new(&3)))
    }

    #[test]
    fn watch_on_conflict() {
        let literals: Vec<Literal> =
            vec![Literal::new(&-24), Literal::new(&-55), Literal::new(&23)];
        let mut clause: Clause = Clause::new(literals);
        let mut model: Vec<Option<Assignment>> = vec![None; 56];
        let opt_asgnmt_f: Option<Assignment> = Some(Assignment {
            polarity: false,
            dl: 0,
            antecedent: None,
        });
        let opt_asgnmt_t: Option<Assignment> = Some(Assignment {
            polarity: true,
            dl: 0,
            antecedent: None,
        });
        model[23] = opt_asgnmt_f;
        model[55] = opt_asgnmt_t;
        model[24] = opt_asgnmt_t;
        println!("Clause before: {:?}", &clause);
        let ans = clause.watch(Literal::new(&-24), &model);
        assert_eq!(ans, Watcher::Conflict);
    }

    #[test]
    fn check_aim() {
        let (cnf, lits) = read_from_string("./test/aim-100-1_6-yes1-1.cnf");
        let result = run_cdcl(cnf, lits);
        match result {
            CdclResult::SAT(_) => println!("\nSAT"),
            CdclResult::UNSAT => panic!("\nUNSAT"),
        }
    }
}

pub mod assignment;
pub mod clause;
pub mod decide_heuristics;
pub mod literal;

use assignment::Assignment;
use clause::Clause;
use decide_heuristics::{
    DecideHeuristic, RandomDecideHeuristic, VariableStateIndependentDecayingSumDecideHeuristic,
};
use literal::Literal;

use std::cmp::{max, min, Reverse};
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use CdclResult::*;

type Queue = VecDeque<Literal>;
type ClauseIndex = usize;

/// Runs the CDCL solver on a given CNF formula.
/// - Initializes the solver with a random heuristic.
/// - Returns `CdclResult` indicating SAT or UNSAT.
pub fn run_cdcl(cnf: &[Vec<i64>], number_of_atoms: usize) -> CdclResult {
    // let decide_heuristic = RandomDecideHeuristic {};
    let decide_heuristic = VariableStateIndependentDecayingSumDecideHeuristic::new(number_of_atoms);
    let mut solver = Cdcl::new(cnf, number_of_atoms, decide_heuristic); // Uses rust RNG
    solver.solve()
}

/// Represents the result of the CDCL solver.
/// - `UNSAT`: The formula is unsatisfiable.
/// - `SAT(Vec<bool>)`: The formula is satisfiable with the given assignment.
#[derive(Debug, PartialEq)]
pub enum CdclResult {
    UNSAT,
    SAT(Vec<bool>),
}

/// Represents the result of unit propagation.
/// - `Unresolved`: No conflicts detected.
/// - `Conflict(ClauseIndex)`: A conflict was found at a specific clause.
enum UnitPropagationResult {
    Unresolved,
    Conflict(ClauseIndex),
}

/// Performs resolution on two clauses using a pivot literal.
/// Generates a new clause without the pivot literal.
fn resolve(clause_a: &Clause, clause_b: &Clause, pivot: Literal) -> Clause {
    let mut seen = std::collections::HashSet::new();
    let mut resolved_lits = Vec::new();
    for lit in clause_a
        .literals
        .iter()
        .chain(clause_b.literals.iter())
        .cloned()
    {
        if lit.variable != pivot.variable {
            // Add to resolved_lits only if not already seen
            if seen.insert(lit) {
                resolved_lits.push(lit);
            }
        }
    }
    Clause::new(resolved_lits)
}

/// Implements the core CDCL solver.
/// - Stores the formula, decision level, assignments, and watched literals.
/// - Uses a heuristic to decide variable assignments.
pub struct Cdcl<H: DecideHeuristic> {
    pub formula: Vec<Clause>,
    pub decision_level: usize,
    model: Vec<Option<Assignment>>,
    clauses_with_lit_watched: HashMap<Literal, HashSet<ClauseIndex>>,
    decide_heuristic: H,
}

impl<H: DecideHeuristic> Cdcl<H> {
    /// Constructs a new CDCL solver.
    /// - Converts the raw CNF formula into internal data structures.
    #[must_use]
    pub fn new(raw_cnf: &[Vec<i64>], number_of_atoms: usize, decide_heuristic: H) -> Self {
        Cdcl {
            formula: Clause::new_vec(raw_cnf),
            decision_level: 0,
            model: vec![None; number_of_atoms + 1],
            clauses_with_lit_watched: HashMap::new(),
            decide_heuristic,
        }
    }

    /// Main solving loop implementing the CDCL algorithm.
    /// Runs unit propagation, decision-making, conflict analysis, and backtracking.
    pub fn solve(&mut self) -> CdclResult {
        // First we get the `formula` and initialize the `watch_pointers` and
        // `clauses_with_lit_watched` with the first two literals of each clause
        self.init_watches();

        // For each clause with a single literal, we add its negation to the queue
        // `to_propagate`, if this variable does not already occur in the `model`
        let mut to_propagate: Queue = VecDeque::new();
        for clause_index in 0..self.formula.len() {
            let clause = &self.formula[clause_index];
            if clause.literals.len() != 1 {
                continue;
            }
            let lit = clause.literals[0];
            if self.model[lit.variable].is_none() {
                // Add to the model
                self.model_assign(lit, Some(clause_index));
                // Propagate it
                to_propagate.push_back(lit);
            }
        }

        // We call the `unit_propagation` method and note the result
        // If reason is "conflict", we have a contradiction, we return UNSAT.
        if let UnitPropagationResult::Conflict(_) = self.unit_propagation(&mut to_propagate) {
            return UNSAT;
        }

        // Until we have a value in `model` for all `formula` variables
        while !self.all_variables_assigned() {
            // We invoke the `decide` method, obtaining a literal
            let lit = self.decide();

            // We increase `decision_level`
            self.decision_level += 1;

            // Add `lit` to the `model`
            self.model_assign(lit, None);

            // We assign `lit` to the `to_propagate` queue
            to_propagate.clear();
            to_propagate.push_back(lit);

            loop {
                // Invoke `unit_propagation`
                match self.unit_propagation(&mut to_propagate) {
                    // If `reason` is not "conflict", we exit the loop to decide again
                    UnitPropagationResult::Unresolved => break,
                    UnitPropagationResult::Conflict(conflict_clause_index) => {
                        // Invoke `conflict_analysis` getting `b` and `learn_clause`
                        match self.conflict_analysis(conflict_clause_index) {
                            None => {
                                // if it fails we return UNSAT
                                return UNSAT;
                            }
                            Some((b, learnt_clause)) => {
                                // Invoke `add_learnt_clause` and `backtrack`
                                let learnt_clause_index = self.add_learnt_clause(&learnt_clause);
                                self.backtrack(b);

                                // Assign `b` as the new decision level
                                self.decision_level = b;

                                // At this point there is only one literal `lit` in `learnt_clause`
                                // and not in `model`
                                let learned_lit: Literal = learnt_clause
                                    .literals
                                    .iter()
                                    .find(|lit| self.model[lit.variable].is_none())
                                    .cloned()
                                    .expect("No literal was learned");

                                // Add `learned_lit` to `model`, with antecedent `learnt_clause`
                                self.model_assign(learned_lit, Some(learnt_clause_index));

                                // `to_propagate` will now be just `learned_lit`
                                to_propagate.clear();
                                to_propagate.push_back(learned_lit);
                            }
                        }
                    }
                }
            }
        }
        self.yield_model()
    }

    /// Initializes watched literals for each clause.
    /// Optimizes unit propagation by reducing clause scans.
    fn init_watches(&mut self) {
        for (clause_index, clause) in self.formula.iter().enumerate() {
            for lit_index in 0..(min(clause.literals.len(), 2)) {
                let lit = clause.literals[lit_index];
                // Add the clause index to the set of
                // clauses observed by this literal
                self.clauses_with_lit_watched
                    .entry(lit)
                    .or_default()
                    .insert(clause_index);
            }
        }
    }

    /// Performs unit propagation to simplify clauses.
    /// Detects conflicts if a clause becomes empty.
    fn unit_propagation(&mut self, to_propagate: &mut Queue) -> UnitPropagationResult {
        // While there are literals to propagate we take `watching_lit`
        while let Some(mut watching_lit) = to_propagate.pop_front() {
            watching_lit = watching_lit.negate();

            // For each `clause` in which `watching_lit` occurs,
            if let Some(clause_indices) = self.clauses_with_lit_watched.get(&watching_lit).cloned()
            {
                for watching_clause_index in clause_indices {
                    let watching_clause = &mut self.formula[watching_clause_index];
                    let mut watched_lits = vec![];
                    for wp_index in watching_clause.watch_pointers {
                        watched_lits.push(watching_clause.literals[wp_index]);
                    }

                    let mut rewatched = false;
                    // For each literal in this `clause`
                    for (lit_index, &lit) in watching_clause.literals.iter().enumerate() {
                        if watched_lits.contains(&lit) {
                            continue;
                        }
                        if let Some(asgnmt) = self.model[lit.variable] {
                            if asgnmt.polarity != lit.polarity {
                                continue;
                            }
                        }
                        // If we find an unobserved `lit` that disagrees with the model
                        // We start observing `lit`, instead of `watching_lit`
                        let idx = watching_clause.get_watch_index(watching_lit);

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
                        break;
                    }
                    if !rewatched {
                        // If there is only one literal watched in `watching_clause`
                        if watching_clause.watch_pointers[0] == watching_clause.watch_pointers[1] {
                            // Return a conflict
                            return UnitPropagationResult::Conflict(watching_clause_index);
                        }
                        // Otherwise we take `other` as the other observed literal.
                        let other: Literal = watching_clause.get_other_watched(watching_lit);

                        match self.model[other.variable] {
                            None => {
                                // If `other` is not defined in the model
                                // We add it to the model
                                self.model_assign(other, Some(watching_clause_index));
                                to_propagate.push_back(other);
                            }
                            Some(asgnmt) => {
                                // If `other` is valid in the model, we continue
                                if asgnmt.polarity == other.polarity {
                                    continue;
                                } else {
                                    // If `other` disagrees with the model, we have a Conflict
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

    /// Checks if all variables have been assigned.
    /// Used as a termination condition for solving.
    fn all_variables_assigned(&self) -> bool {
        for lit in self.model.iter().skip(1) {
            if lit.is_none() {
                return false;
            }
        }
        true
    }

    /// Analyzes conflicts to determine the backtrack level.
    /// Returns the decision level and learned clause if applicable.
    fn conflict_analysis(&self, conflict_clause_index: ClauseIndex) -> Option<(usize, Clause)> {
        if self.decision_level == 0 {
            return None;
        }

        let conflict_clause = &self.formula[conflict_clause_index];

        // For each `literal` of the `conflict clause`
        // Whose decision level is the current one
        let mut literals: Queue = conflict_clause
            .literals
            .iter()
            .filter(|lit| match self.model[lit.variable] {
                None => false,
                Some(asgnmt) => asgnmt.dl == self.decision_level,
            })
            .copied()
            .collect();

        let mut learnt_clause = conflict_clause.clone();

        while literals.len() > 1 {
            // And the antecedent exists i.e. it was propagated
            literals.retain(|lit| {
                self.model[lit.variable]
                    .expect("Conflict should be assigned for all variables")
                    .antecedent
                    .is_some()
            });
            let literal = literals.pop_front();
            if literal.is_none() {
                break;
            }
            let literal = literal.unwrap();

            // We take its `antecedent` i.e. the literals of the unit clause that propagated this literal
            let antecedent = &self.model[literal.variable]?.antecedent;
            if antecedent.is_none() {
                break;
            }
            let antecedent = &self.formula[antecedent.unwrap()];

            // We calculate the `resolution` of `learnt_clause` and `antecedent` with `literal` pivot
            // The resolved clause is the new conflicting clause, called "learnt_clause"
            learnt_clause = resolve(&learnt_clause, antecedent, literal);

            // Filter the current decision_level
            literals = learnt_clause
                .literals
                .iter()
                .filter(|lit| match self.model[lit.variable] {
                    None => false,
                    Some(asgnmt) => asgnmt.dl == self.decision_level,
                })
                .copied()
                .collect();
        }

        // We have a learned clause `learnt_clause`
        // We analyze the decision level of the literals contained in this clause

        // If they are all the same, we return b = 0 and learnt_clause
        // Otherwise, we calculate b for the (second) highest decision level in learned_clause
        let mut b = 0;
        for lit in &learnt_clause.literals {
            match self.model[lit.variable] {
                None => continue,
                Some(asgnmt) => {
                    if asgnmt.dl < self.decision_level {
                        // Store the highest decision level found,
                        // when smaller than `self.decision_level`
                        b = max(b, asgnmt.dl);
                    }
                }
            }
        }
        Some((b, learnt_clause))
    }

    /// Adds a newly learned clause to the formula and updates watched literals.
    /// Returns the index of the new clause.
    fn add_learnt_clause(&mut self, learnt_clause: &Clause) -> ClauseIndex {
        let new_clause_id = self.formula.len();
        // Add `learnt clause` to the formula clauses
        self.formula.push(learnt_clause.clone());

        // Call signal used in heuristics
        self.decide_heuristic.clause_added_signal(learnt_clause);

        // If there is only one literal in the clause we are done
        if learnt_clause.literals.len() < 2 {
            let lit = learnt_clause.literals[0];
            self.clauses_with_lit_watched
                .entry(lit)
                .or_default()
                .insert(new_clause_id);
            self.formula[new_clause_id].watch_pointers[0] = 0;
            return new_clause_id;
        }
        // Assign `watch_pointers` to the two literals of `learnt_clause`
        // with higher decision level
        let mut heap_of_two = BinaryHeap::with_capacity(2);
        for (literal_index, literal) in learnt_clause.literals.iter().enumerate() {
            if let Some(asgnmt) = self.model[literal.variable] {
                // Keep the best two in the heap
                heap_of_two.push(Reverse((asgnmt.dl, literal, literal_index)));
                while heap_of_two.len() > 2 {
                    heap_of_two.pop();
                }
            }
        }
        for (i, Reverse((_, to_watch_lit, lit_index))) in heap_of_two.into_vec().iter().enumerate()
        {
            // Update `clauses_with_lit_watched` with `learnt_clause` for these literals
            self.clauses_with_lit_watched
                .entry(**to_watch_lit)
                .or_default()
                .insert(new_clause_id);
            self.formula[new_clause_id].watch_pointers[i] = *lit_index;
        }

        new_clause_id
    }

    /// Backtracks to a given decision level, undoing assignments above it.
    fn backtrack(&mut self, b: usize) {
        for (i, oas) in self.model.iter_mut().enumerate() {
            if let Some(asgnmt) = oas {
                if asgnmt.dl > b {
                    *oas = None;
                    self.decide_heuristic.variable_unassigned_signal(i);
                }
            }
        }
    }

    /// Chooses the next variable to assign using the heuristic.
    /// Panics if no unassigned variables remain.
    fn decide(&mut self) -> Literal {
        let polarity = self.decide_heuristic.next_polarity();
        let variable = self
            .decide_heuristic
            .next_variable(&self.model)
            .expect("decide can't pick an unassigned variable!");
        let lit: Literal = Literal { variable, polarity };
        lit
    }

    /// Assigns a value to a variable and records its antecedent if applicable.
    fn model_assign(&mut self, lit: Literal, antecedent: Option<ClauseIndex>) {
        self.model[lit.variable] = Some(Assignment {
            polarity: lit.polarity,
            antecedent,
            dl: self.decision_level,
        });
        self.decide_heuristic.variable_assigned_signal(lit.variable);
    }

    /// Returns the current model as a satisfying assignment if the formula is satisfiable.
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
    use core::panic;

    use crate::parser::read_from_string;
    use decide_heuristics::MockDecideHeuristic;
    use mockall::*;

    use super::*;

    fn check_model(cnf: &Vec<Vec<i64>>, model: &Vec<bool>) -> bool {
        // Check that the model satisfies the CNF
        for clause in cnf {
            let mut clause_satisfied = false;
            for literal in clause {
                let variable = literal.unsigned_abs() as usize;
                // Ensure the variable index is within bounds of the model
                if variable > model.len() {
                    panic!("Variable {} is out of bounds for the model", variable);
                }
                // Check if the literal is satisfied by the model
                if (*literal > 0 && model[variable - 1]) || (*literal < 0 && !model[variable - 1]) {
                    clause_satisfied = true;
                    break;
                }
            }
            if !clause_satisfied {
                println!(
                    "Clause {:?} is not satisfied by the model {:?}",
                    clause, model
                );
                return false;
            }
        }
        true
    }

    fn get_trace<H: DecideHeuristic>(_solver: &Cdcl<H>) {
        println!("Try this decision to trace it:");
        print!("let polarities = vec![");
        // ? Needs decision bookkeeping to work...
        println!("];\n");
    }

    #[cfg(test)]
    fn setup_mock(polarities: Vec<bool>, variables: Vec<usize>) -> MockDecideHeuristic {
        use rand::seq::IteratorRandom;

        let mut mock_decide_heuristic = MockDecideHeuristic::new();

        mock_decide_heuristic
            .expect_variable_assigned_signal()
            .return_const(());
        mock_decide_heuristic
            .expect_variable_unassigned_signal()
            .return_const(());
        mock_decide_heuristic
            .expect_clause_added_signal()
            .return_const(());

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
            .returning(rand::random::<bool>);

        // Setup answers for `next_variable()`
        let mut sequence = Sequence::new();
        for var in variables {
            mock_decide_heuristic
                .expect_next_variable()
                .times(1)
                .in_sequence(&mut sequence)
                .return_const(var);
        }

        if true {
            mock_decide_heuristic
                .expect_next_variable()
                .times(..)
                .returning(|model| {
                    let mut rng = rand::thread_rng();
                    // Collect indices of unassigned variables (where model[index] is None)
                    let unassigned_indices: Vec<usize> = model
                        .iter()
                        .enumerate()
                        .filter_map(|(index, value)| {
                            if value.is_none() && index != 0 {
                                Some(index)
                            } else {
                                None
                            }
                        })
                        .collect();
                    // Randomly select one of the unassigned indices
                    unassigned_indices.into_iter().choose(&mut rng)
                });
        }

        mock_decide_heuristic
    }

    #[test]
    fn contradiction_is_unsat() {
        let cnf = vec![vec![1], vec![-1]];
        let result = run_cdcl(&cnf, 3);
        assert_eq!(result, UNSAT);
    }

    #[test]
    fn empty_cnf_is_sat() {
        let cnf = vec![];
        let mut solver = Cdcl::new(&cnf, 2, RandomDecideHeuristic {});
        let result = solver.solve();
        match result {
            UNSAT => {
                get_trace(&solver);
                panic!("Expected SAT");
            }
            SAT(model) => {
                let passed = check_model(&cnf, &model);
                if !passed {
                    get_trace(&solver);
                }
            }
        }
    }

    #[test]
    fn single_cnf_is_sat() {
        let cnf = vec![vec![1]];
        let mut solver = Cdcl::new(&cnf, 2, RandomDecideHeuristic {});
        let result = solver.solve();
        match result {
            SAT(model) => {
                check_model(&cnf, &model);
            }
            UNSAT => {
                get_trace(&solver);
                panic!("single cnf is sat");
            }
        }
    }

    #[test]
    fn two_cnf_is_sat() {
        let cnf = vec![vec![1, 2], vec![-1, -2]];
        let polarities = vec![false];
        let variables = vec![2];
        let mock_decide_heuristic = setup_mock(polarities, variables);
        let mut solver = Cdcl::new(&cnf, 2, mock_decide_heuristic);
        let result = solver.solve();
        match result {
            SAT(model) => {
                let passed = check_model(&cnf, &model);
                if !passed {
                    get_trace(&solver);
                }
            }
            UNSAT => {
                get_trace(&solver);
                panic!("two cnf is sat fail");
            }
        }
    }

    #[test]
    fn two_cnf_is_unsat() {
        let cnf = vec![vec![1, 2], vec![-1, -2], vec![1, -2], vec![-1, 2]];
        let polarities = vec![false];
        let variables = vec![2];
        let mock_decide_heuristic = setup_mock(polarities, variables);
        let mut solver = Cdcl::new(&cnf, 2, mock_decide_heuristic);
        let result = solver.solve();
        match result {
            UNSAT => println!("OK"),
            SAT(model) => {
                let passed = check_model(&cnf, &model);
                if !passed {
                    get_trace(&solver);
                }
            }
        }
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
        let mut solver = Cdcl::new(&original_cnf, 6, decide_heuristic);
        // TODO: implement pre_process
        // solver.pre_process(original_cnf);
        // assert_eq!(0, solver.formula.len())
        match solver.solve() {
            UNSAT => {
                get_trace(&solver);
                panic!("Expected SAT");
            }
            SAT(model) => {
                if !check_model(&original_cnf, &model) {
                    get_trace(&solver);
                    panic!("Model does not solve!");
                }
            }
        }
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
        let _solver = Cdcl::new(&original_cnf, 7, mock_decide_heuristic);
        let _target_cnf: Vec<Vec<i64>> = vec![
            //must remove clauses with 1 (verified by unit clause) or -2 (verified by pure)
            vec![-7, 6],
            vec![5, 7],
            vec![-1, 4, 5],
            vec![-6, -4, -3],
            vec![-5, -3, 4],
        ];

        // TODO
        // let _ = solver.pre_process(original_cnf);

        // for (i, c) in solver.formula.iter().enumerate() {
        //     for (j, &lit) in c.literals.iter().enumerate() {
        //         assert_eq!(lit, Literal::new(&target_cnf[i][j]));
        //     }
        // }
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
        let lits = 6;

        let vsids = VariableStateIndependentDecayingSumDecideHeuristic::new(lits);
        let mut solver = Cdcl::new(&cnf, lits, vsids);
        let result = solver.solve();
        match result {
            SAT(model) => {
                let passed = check_model(&cnf, &model);
                if !passed {
                    get_trace(&solver);
                }
            }
            UNSAT => {
                get_trace(&solver);
                panic!("backtrack small case fail")
            }
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
        let mut solver = Cdcl::new(&cnf, 9, mock_decide_heuristic);
        let result = solver.solve();
        // TODO: Assertions missing
        match result {
            UNSAT => println!("OK"),
            SAT(model) => println!("We got sat...{:?}", model),
        }
    }

    #[test]
    fn check_dubois20() {
        let (cnf, lits) = read_from_string("./test/dubois20.cnf");

        let polarities = vec![
            true, false, false, true, false, false, false, false, false, false, true, false, true,
            false, false, false, true, false, false, true, true,
        ];

        let variables = vec![
            18, 28, 47, 29, 48, 39, 55, 8, 32, 3, 46, 22, 54, 59, 43, 35, 53, 24, 16, 42, 58,
        ];

        let mock_decide_heuristic = setup_mock(polarities, variables);

        let vsids = VariableStateIndependentDecayingSumDecideHeuristic::new(lits);

        let mut solver = Cdcl::new(&cnf, lits, vsids);
        let result = solver.solve();
        match result {
            CdclResult::SAT(model) => {
                check_model(&cnf, &model);
                get_trace(&solver);
                panic!("EXPECTED UNSAT!");
            }
            CdclResult::UNSAT => println!("UNSAT"),
        }
    }

    #[test]
    fn check_aim() {
        let (cnf, lits) = read_from_string("./test/aim-100-1_6-yes1-1.cnf");
        let mut solver = Cdcl::new(&cnf, lits, RandomDecideHeuristic {});
        let result = solver.solve();
        match result {
            CdclResult::SAT(model) => {
                let passed = check_model(&cnf, &model);
                if !passed {
                    get_trace(&solver);
                    panic!("Model not ok!");
                }
            }
            CdclResult::UNSAT => {
                get_trace(&solver);
                panic!("\nUNSAT")
            }
        }
    }
}

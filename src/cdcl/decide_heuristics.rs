use std::collections::{BTreeSet, BinaryHeap, HashMap};

// For random Heuristic
use rand::prelude::IteratorRandom;
use rand::Rng;

// For Testing
use mockall::predicate::*;
use mockall::*;

use super::assignment::Assignment;
use super::clause::Clause;
use super::literal::Literal;

/// Defines an interface for decision heuristics.
/// Provides methods to choose a random variable and its polarity.
#[automock]
pub trait DecideHeuristic {
    ///
    /// Gets a the next literal following the heuristic
    fn next_literal(&self, model: &[Option<Assignment>]) -> Option<Literal>;
    /// Used in heuristic
    fn clause_added_signal(&mut self, _clause: &Clause) {}
    fn variable_assigned_signal(&mut self, _variable: usize) {}
    fn variable_unassigned_signal(&mut self, _variable: usize) {}
}

/// Implements a random decision heuristic.
/// Uses Rust's RNG to select variable assignments.
pub struct RandomDecideHeuristic {}

impl DecideHeuristic for RandomDecideHeuristic {
    fn next_literal(&self, model: &[Option<Assignment>]) -> Option<Literal> {
        let mut rng = rand::thread_rng();
        let polarity = rng.gen();

        // Collect indices of unassigned variables (where model[index] is None)
        let unassigned_indices: Vec<usize> = model
            .iter()
            .enumerate()
            .filter_map(
                |(index, value)| {
                    if value.is_none() {
                        Some(index)
                    } else {
                        None
                    }
                },
            )
            .collect();

        // Randomly select one of the unassigned indices
        unassigned_indices
            .into_iter()
            .choose(&mut rng)
            .map(|variable| Literal { variable, polarity })
    }
}

/// Variable State Independent Decaying Sum (VSIDS) is described as follows:
/// (1) Each variable in each polarity has a counter, initialized to 0.
/// (2) When a clause is added to the database, the counter associated with each
/// literal in the clause is incremented.
/// (3) The (unassigned) variable and polarity with the highest counter is chosen
/// at each decision.
/// (4) Ties are broken randomly by default, although this is configurable
/// (5) Periodically, all the counters are divided by a constant
type Score = usize;
pub struct VariableStateIndependentDecayingSumDecideHeuristic {
    counter: HashMap<Literal, Score>,
    on: BTreeSet<(Score, Literal)>,
    off: BTreeSet<(Score, Literal)>,
}

impl VariableStateIndependentDecayingSumDecideHeuristic {
    #[must_use]
    pub fn new(variables: usize) -> Self {
        let mut counter = HashMap::new();
        for variable in 1..=variables {
            for polarity in [false, true] {
                let literal = Literal { variable, polarity };
                counter.insert(literal, 0);
            }
        }
        VariableStateIndependentDecayingSumDecideHeuristic {
            counter,
            on: BTreeSet::new(),
            off: BTreeSet::new(),
        }
    }

    fn turn_off(&mut self, lit: Literal) {
        let count = *self.counter.entry(lit).or_default();
        let entry = (count, lit);
        // remove from on
        self.on.remove(&entry);
        // add to off
        self.off.insert(entry);
    }

    fn turn_on(&mut self, lit: Literal) {
        let count = self.counter.get(&lit).copied().unwrap_or_default();
        let entry = (count, lit);
        // remove from off
        self.off.remove(&entry);
        // add to on
        self.on.insert(entry);
    }

    fn increment(&mut self, lit: Literal) {
        // TODO: Update the `on`/`off` sets for the new count
        *self.counter.entry(lit).or_default() += 1;
    }
}

impl DecideHeuristic for VariableStateIndependentDecayingSumDecideHeuristic {
    ///The (unassigned) variable and polarity with the highest
    /// counter is chosen at each decision.
    fn next_literal(&self, _model: &[Option<Assignment>]) -> Option<Literal> {
        self.on.iter().next_back().map(|&(_, lit)| lit)
    }

    /// When a clause is added to the database, the counter associated
    /// with each literal in the clause is incremented.
    fn clause_added_signal(&mut self, clause: &Clause) {
        for lit in &clause.literals {
            // *self.counter.entry(*lit).or_insert(0) += 1;
            self.increment(*lit);
        }
    }

    fn variable_assigned_signal(&mut self, variable: usize) {
        for polarity in [false, true] {
            let lit = Literal { variable, polarity };
            self.turn_on(lit);
        }
    }

    fn variable_unassigned_signal(&mut self, variable: usize) {
        for polarity in [false, true] {
            let lit = Literal { variable, polarity };
            self.turn_off(lit);
        }
    }
}

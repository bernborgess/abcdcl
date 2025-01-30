use std::collections::{BinaryHeap, HashMap};

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
    /// Gets a random boolean
    fn next_polarity(&self) -> bool;
    /// Gets a random variable, if any exist
    fn next_variable(&self, model: &[Option<Assignment>]) -> Option<usize>;
    /// Used in heuristic
    fn clause_added_signal(&mut self, _clause: &Clause) {}
    fn variable_assigned_signal(&mut self, _variable: usize) {}
    fn variable_unassigned_signal(&mut self, _variable: usize) {}
}

/// Implements a random decision heuristic.
/// Uses Rust's RNG to select variable assignments.
pub struct RandomDecideHeuristic {}

impl DecideHeuristic for RandomDecideHeuristic {
    fn next_polarity(&self) -> bool {
        let mut rng = rand::thread_rng();
        rng.gen()
    }

    fn next_variable(&self, model: &[Option<Assignment>]) -> Option<usize> {
        let mut rng = rand::thread_rng();

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
        unassigned_indices.into_iter().choose(&mut rng)
    }
}

//
use std::cmp::Ordering;

/// Represents a variable in the decision heap.
#[derive(Eq, PartialEq, Clone)]
struct HeapEntry {
    literal: Literal,
    counter: usize,
    assigned: bool,
}

impl Ord for HeapEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.assigned, other.assigned) {
            (false, true) => Ordering::Greater, // Unassigned > Assigned
            (true, false) => Ordering::Less,
            _ => self.counter.cmp(&other.counter), // Compare counters if both are same assignment status
        }
    }
}

impl PartialOrd for HeapEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
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
pub struct VariableStateIndependentDecayingSumDecideHeuristic {
    counter: HashMap<Literal, usize>,
    highest_counter_heap: BinaryHeap<HeapEntry>,
    heap_entries: HashMap<Literal, HeapEntry>,
}

impl VariableStateIndependentDecayingSumDecideHeuristic {
    #[must_use]
    pub fn new(variables: usize) -> Self {
        let mut counter = HashMap::new();
        let mut highest_counter_heap = BinaryHeap::new();
        let mut heap_entries = HashMap::new();
        for variable in 1..=variables {
            for polarity in [false, true] {
                let literal = Literal { variable, polarity };
                let entry = HeapEntry {
                    literal,
                    counter: 0,
                    assigned: false,
                };
                heap_entries.insert(literal, entry.clone());
                highest_counter_heap.push(entry);
                counter.insert(literal, 0);
            }
        }
        VariableStateIndependentDecayingSumDecideHeuristic {
            counter,
            highest_counter_heap,
            heap_entries,
        }
    }

    fn update_variable_entry(
        &mut self,
        variable: usize,
        new_counter: Option<usize>,
        new_assigned: Option<bool>,
    ) {
        for polarity in [false, true] {
            let literal = Literal { variable, polarity };

            // Get old entry
            let mut entry = self.heap_entries.remove(&literal).unwrap_or(HeapEntry {
                literal,
                counter: 0,
                assigned: false,
            });

            // Remove old heap entry
            self.highest_counter_heap.retain(|e| e.literal == literal);

            // Update fields
            if let Some(counter) = new_counter {
                entry.counter += counter;
            }
            if let Some(assigned) = new_assigned {
                entry.assigned = assigned;
            }

            // Put back in heap and hash map
            self.highest_counter_heap.push(entry.clone());
            self.heap_entries.insert(literal, entry);
        }
    }

    fn update_variable_assignment(&mut self, variable: usize, assigned: bool) {
        self.update_variable_entry(variable, None, Some(assigned));
    }
}

impl DecideHeuristic for VariableStateIndependentDecayingSumDecideHeuristic {
    ///The (unassigned) variable and polarity with the highest
    /// counter is chosen at each decision.
    fn next_polarity(&self) -> bool {
        self.highest_counter_heap
            .peek()
            .map(|e| e.literal.polarity)
            .unwrap_or_default()
    }

    fn next_variable(&self, model: &[Option<Assignment>]) -> Option<usize> {
        self.highest_counter_heap.peek().map(|e| e.literal.variable)
    }

    /// When a clause is added to the database, the counter associated
    /// with each literal in the clause is incremented.
    fn clause_added_signal(&mut self, clause: &Clause) {
        for lit in &clause.literals {
            self.update_variable_entry(lit.variable, Some(1), None);
        }
    }

    fn variable_assigned_signal(&mut self, variable: usize) {
        self.update_variable_assignment(variable, true);
    }

    fn variable_unassigned_signal(&mut self, variable: usize) {
        self.update_variable_assignment(variable, false);
    }
}

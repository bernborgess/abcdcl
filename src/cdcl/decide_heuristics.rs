// For random Heuristic
use rand::prelude::IteratorRandom;
use rand::Rng;

// For Testing
use mockall::predicate::*;
use mockall::*;

use super::assignment::Assignment;

/// Defines an interface for decision heuristics.
/// Provides methods to choose a random variable and its polarity.
#[automock]
pub trait DecideHeuristic {
    /// Gets a random boolean
    fn next_polarity(&self) -> bool;
    /// Gets a random variable, if any exist
    fn next_variable(&self, model: &[Option<Assignment>]) -> Option<usize>;
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

/// Represents different states of a watched literal in the clause.
/// - `Unit(Literal)`: The clause has become a unit, propagating the literal.
/// - `Watched(Literal)`: The given literal is actively watched.
/// - `Satisfied(Literal)`: The clause is already satisfied.
/// - `Conflict`: Indicates a conflict in the clause.
#[derive(Debug, PartialEq)]
pub enum Watcher {
    Unit(Literal),
    Watched(Literal),
    Satisfied(Literal),
    Conflict,
}

use super::literal::Literal;

/// Represents a clause in the CNF formula.
/// - `literals`: The list of literals in the clause.
/// - `watch_pointers`: Indices of the two watched literals for efficient unit propagation.
#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub watch_pointers: [usize; 2],
}

impl Clause {
    /// Constructs a new clause with given literals.
    /// Initializes watch pointers to the first two literals if available.
    pub fn new(literals: Vec<Literal>) -> Clause {
        let arr = if literals.len() == 1 { [0, 0] } else { [0, 1] };
        Clause {
            literals,
            watch_pointers: arr,
        }
    }

    /// Converts a CNF formula (vector of integer vectors) into a vector of `Clause` objects.
    pub fn new_vec(arr: &[Vec<i64>]) -> Vec<Clause> {
        arr.iter()
            .map(|v| v.iter().map(Literal::new).collect())
            .map(Clause::new)
            .collect()
    }

    /// Returns the index (0 or 1) of the watch pointer that matches the given literal.
    pub fn get_watch_index(&self, lit: Literal) -> usize {
        if self.literals[self.watch_pointers[0]] == lit {
            0
        } else {
            1
        }
    }

    /// Returns the other watched literal given one of the watched literals.
    pub fn get_other_watched(&self, lit: Literal) -> Literal {
        let other_idx = 1 - self.get_watch_index(lit);
        self.literals[self.watch_pointers[other_idx]]
    }
}

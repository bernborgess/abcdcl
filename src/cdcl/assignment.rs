use super::ClauseIndex;

/// Represents an assignment in the model.
/// - `polarity`: Boolean indicating whether the literal is set to positive (`true`) or negated (`false`).
/// - `antecedent`: The index of the clause that implied this assignment, or none.
/// - `dl`: The decision level at which this assignment was created.
#[derive(Clone, Copy, Debug)]
pub struct Assignment {
    pub polarity: bool,
    pub antecedent: Option<ClauseIndex>,
    pub dl: usize,
}

impl Assignment {
    pub fn new(polarity: bool, dl: usize, antecedent: Option<ClauseIndex>) -> Assignment {
        Assignment {
            polarity,
            antecedent,
            dl,
        }
    }
}

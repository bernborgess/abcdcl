use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Literal {
    variable: i32,
    negation: bool,
}

impl Literal {
    // Constructor to create a new Literal
    pub fn new(variable: i32, negation: bool) -> Self {
        Literal { variable, negation }
    }

    // Method to return the negation of the literal
    pub fn negation(self) -> Self {
        Literal {
            variable: self.variable,
            negation: !self.negation,
        }
    }
}

// Implement the `Display` trait for `Literal`
impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.negation {
            write!(f, "¬{}", self.variable)
        } else {
            write!(f, "{}", self.variable)
        }
    }
}

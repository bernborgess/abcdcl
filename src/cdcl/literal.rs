use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Literal {
    pub variable: usize,
    pub polarity: bool,
}

impl Literal {
    // Constructor to create a new Literal
    pub fn new(val: &i64) -> Self {
        if *val == 0 {
            panic!("0 cannot be a literal");
        }
        Literal {
            variable: val.unsigned_abs() as usize,
            polarity: *val > 0,
        }
    }

    // Method to return the negation of the literal
    pub fn negate(self) -> Self {
        Literal {
            variable: self.variable,
            polarity: !self.polarity,
        }
    }
}

// Implement the `Display` trait for `Literal`
impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.polarity {
            write!(f, "{}", self.variable)
        } else {
            write!(f, "¬{}", self.variable)
        }
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.polarity {
            write!(f, "{}", self.variable)
        } else {
            write!(f, "¬{}", self.variable)
        }
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.polarity, other.polarity) {
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (true, true) => self.variable.cmp(&other.variable),
            (false, false) => other.variable.cmp(&self.variable),
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

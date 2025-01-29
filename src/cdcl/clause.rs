#[derive(Debug, PartialEq)]
pub enum Watcher {
    Unit(Literal),      // Literal diz quem propagar
    Watched(Literal),   // Literal diz quem é o novo vigiado
    Satisfied(Literal), // Literal diz que é o novo vigiado, se o literal for igual ao que chamou watch, não há novo vigiado
    Conflict,
}

use super::literal::Literal;

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub watch_pointers: [usize; 2],
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Clause {
        let arr = if literals.len() == 1 { [0, 0] } else { [0, 1] };
        Clause {
            literals,
            watch_pointers: arr,
        }
    }

    pub fn new_vec(arr: &[Vec<i64>]) -> Vec<Clause> {
        arr.iter()
            .map(|v| v.iter().map(Literal::new).collect())
            .map(Clause::new)
            .collect()
    }
}

use std::collections::HashSet;
use std::fmt;

pub enum Watcher {
    Unit(Literal),
    Watched(Literal),
    Satisfied(Literal),
    Conflict,
}

use super::{assignment::Assignment, literal::Literal};

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    watch_ptr: [usize; 2],
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, lit) in self.literals.iter().enumerate() {
            if (self.watch_ptr[0] == i) || (self.watch_ptr[1] == i) {
                write!(f, "•")?;
            }
            write!(f, "{:?},", lit)?;
        }
        writeln!(f)
    }
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Clause {
        Clause {
            literals,
            watch_ptr: [0, 1],
        }
    }

    pub fn new_vec(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| v.iter().map(|x| Literal::new(&x)).collect())
            .map(Clause::new)
            .collect()
    }

    pub fn watch(&mut self, lit: Literal, model: &[Option<Assignment>]) -> Watcher {
        // trato cláusulas unitárias
        if self.literals.len() == 1 {
            match self.model_agreement(model, lit) {
                Some(true) => Watcher::Satisfied(lit),
                Some(false) => Watcher::Conflict,
                None => Watcher::Unit(lit),
            }
        } else {
            let val_0: Literal = self.point(0).unwrap();
            let val_1: Literal = self.point(1).unwrap();
            //verifica se a cláusula já está satisfeita
            if let Some(true) = self.model_agreement(model, val_0) {
                Watcher::Satisfied(lit)
            } else if let Some(true) = self.model_agreement(model, val_0) {
                return Watcher::Satisfied(lit);
            } else {
                let pointer_to_lit = if val_0 == lit {
                    0
                } else if val_1 == lit {
                    1
                } else {
                    eprintln!("Clause: {:?}", &self);
                    eprintln!("lit: {lit}");
                    eprintln!("model: {:?}", model);
                    panic!("The literal {:?} is not being watched here", lit);
                };
                self.next(pointer_to_lit, model)
            }
        }
    }

    // tenta incrementar o ponteiro watch_ptr[pointer_to_lit]
    fn next(&mut self, pointer_to_lit: usize, model: &[Option<Assignment>]) -> Watcher {
        let max_pointer = std::cmp::max(self.watch_ptr[0], self.watch_ptr[1]);

        // incrementar o ponteiro faria ele ultrapassar o array
        // retorna o literal que sobrou para ser propagado
        if max_pointer == self.literals.len() - 1 {
            Watcher::Unit(self.point((pointer_to_lit + 1) % 2).unwrap())
        } else {
            // incrementa o ponteiro
            self.watch_ptr[pointer_to_lit] = max_pointer + 1;
            let candidate = self.point(pointer_to_lit).unwrap();
            match self.model_agreement(model, candidate) {
                Some(true) => Watcher::Satisfied(candidate),
                Some(false) => self.next(pointer_to_lit, model),
                None => Watcher::Watched(candidate),
            }
        }
    }

    fn model_agreement(&self, model: &[Option<Assignment>], lit: Literal) -> Option<bool> {
        model[lit.variable].map(|assignment| assignment.polarity == lit.polarity)
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> Option<Literal> {
        self.literals.get(self.watch_ptr[i]).copied()
    }

    pub fn resolution(&self, other: &Clause, pivot: Literal) -> Clause {
        let mut first: Vec<Literal> = self
            .literals
            .iter()
            .filter(|&x| x != &pivot)
            .cloned()
            .collect();
        let second: Vec<Literal> = other.literals.clone();
        //println!("Resolving on pivot {:?}: ", &pivot);
        //println!("{:?}", &self.literals);
        //println!("{:?}", &second);
        let mut seen: HashSet<Literal> = first.iter().cloned().collect();
        seen.remove(&pivot);
        seen.remove(&pivot.negate());

        for &item in second.iter() {
            //só insere se o item não está no conjunto e não é o pivo
            if (!seen.contains(&item)) && (item.variable != pivot.variable) {
                first.push(item);
            }
        }
        //println!("Result:");
        //println!("{:?}\n", &first);
        Clause {
            literals: first,
            watch_ptr: [0, 1],
        }
    }
}

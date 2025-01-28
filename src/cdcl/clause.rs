use std::collections::HashSet;
use std::fmt;
#[derive(Debug, PartialEq)]
pub enum Watcher {
    Unit(Literal),      // Literal diz quem propagar
    Watched(Literal),   // Literal diz quem é o novo vigiado
    Satisfied(Literal), // Literal diz que é o novo vigiado, se o literal for igual ao que chamou watch, não há novo vigiado
    Conflict,
}

use crate::cdcl::utils::print_model;

use super::{assignment::Assignment, literal::Literal};

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    pub watch_pointers: [usize; 2],
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, lit) in self.literals.iter().enumerate() {
            if (self.watch_pointers[0] == i) || (self.watch_pointers[1] == i) {
                write!(f, "•")?;
            }
            write!(f, "{:?},", lit)?;
        }
        writeln!(f)
    }
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Clause {
        let arr = if literals.len() == 1 { [0, 0] } else { [0, 1] };
        Clause {
            literals,
            watch_pointers: arr,
        }
    }

    pub fn new_vec(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| v.iter().map(|x| Literal::new(&x)).collect())
            .map(Clause::new)
            .collect()
    }

    pub fn is_conflict(&self, model: &[Option<Assignment>]) -> bool {
        self.literals
            .iter()
            .fold(true, |x, lit| model[lit.variable].is_some() && x)
    }

    pub fn watch(&mut self, lit: Literal, model: &[Option<Assignment>]) -> Watcher {
        //println!("watching {:?}", &lit);
        //print_model(model);
        // trato cláusulas unitárias
        if self.literals.len() == 1 {
            match self.model_agreement(model, lit) {
                Some(false) => Watcher::Conflict,
                _ => panic!(
                    "Se uma cláusula unitária está sendo propagada, seu literal devia ser falso"
                ),
                /*Some(true) => Watcher::Satisfied(lit),
                None => Watcher::Unit(lit, None),*/
            }
        } else {
            let val_0: Literal = self.point(0).unwrap();
            let val_1: Literal = self.point(1).unwrap();
            //verifica se a cláusula já está satisfeita
            if let Some(true) = self.model_agreement(model, val_0) {
                // Aqui e no próximo if let, Satisfied retorna lit mesmo se o literal que satisfaz é o outro literal vigiado
                // Isso serve pra avisar o propagate que essa cláusula já estava satisfeita e portanto os ponteiros não andaram
                Watcher::Satisfied(lit)
            } else if let Some(true) = self.model_agreement(model, val_1) {
                Watcher::Satisfied(lit)
            } else {
                let pointer_to_lit = if val_0 == lit {
                    0
                } else if val_1 == lit {
                    1
                } else {
                    panic!("The literal {:?} is not being watched here", lit);
                };

                self.walk(pointer_to_lit, model)
            }
        }
    }

    fn walk(&mut self, pointer_to_lit: usize, model: &[Option<Assignment>]) -> Watcher {
        let n: usize = self.literals.len();
        let fixed_lit = self.point(1 - pointer_to_lit).unwrap();
        let original_lit: Literal = self.point(pointer_to_lit).unwrap();
        let pointer_to_avoid: usize = self.watch_pointers[1 - pointer_to_lit];
        let mut next: usize = self.watch_pointers[pointer_to_lit];
        loop {
            next = if ((next + 1) % n) == pointer_to_avoid {
                (next + 2) % n
            } else {
                (next + 1) % n
            };
            self.watch_pointers[pointer_to_lit] = next;
            let watched_lit: Literal = self.point(pointer_to_lit).unwrap();
            if watched_lit != original_lit {
                match self.model_agreement(model, watched_lit) {
                    Some(true) => return Watcher::Satisfied(watched_lit),
                    Some(false) => (),
                    None => return Watcher::Watched(watched_lit),
                }
            } else {
                match self.model_agreement(model, fixed_lit) {
                    Some(true) => panic!("Devia ter retornado satisfied no watch"),
                    Some(false) => return Watcher::Conflict,
                    None => return Watcher::Unit(fixed_lit),
                }
            }
        }
    }

    // Some(true) se o modelo concorda, Some(false) se ele discorda, None se ele não acha nada
    fn model_agreement(&self, model: &[Option<Assignment>], lit: Literal) -> Option<bool> {
        model[lit.variable].map(|assignment| assignment.polarity == lit.polarity)
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> Option<Literal> {
        self.literals.get(self.watch_pointers[i]).copied()
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
            watch_pointers: [0, 1],
        }
    }
}

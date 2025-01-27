use std::collections::HashSet;
use std::fmt;
#[derive(Debug)]
pub enum Watcher {
    Unit(Literal),      // Literal diz quem propagar,
    Watched(Literal),   // Literal diz quem é o novo vigiado
    Satisfied(Literal), // Literal diz que é o novo vigiado, se o literal for igual ao que chamou watch, não há novo vigiado
    Conflict(Literal),  // Literal diz a
}

use crate::cdcl::utils::print_model;

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
        //println!("watching {:?}", &lit);
        // trato cláusulas unitárias
        if self.literals.len() == 1 {
            match self.model_agreement(model, lit) {
                Some(true) => Watcher::Satisfied(lit),
                Some(false) => Watcher::Conflict(lit),
                None => Watcher::Unit(lit),
            }
        } else {
            let val_0: Literal = self.point(0).unwrap();
            let val_1: Literal = self.point(1).unwrap();
            //verifica se a cláusula já está satisfeita
            if let Some(true) = self.model_agreement(model, val_0) {
                // Aqui o e no próximo if let, Satisfied retorna lit mesmo se o literal que satisfaz é o outro literal vigiado
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
                    //eprintln!("Clause: {:?}", &self);
                    //eprintln!("lit: {lit}");
                    //print_model(model);
                    panic!("The literal {:?} is not being watched here", lit);
                };
                self.next(pointer_to_lit, model, true)
            }
        }
    }

    // tenta incrementar o ponteiro watch_ptr[pointer_to_lit]
    fn next(
        &mut self,
        pointer_to_lit: usize,
        model: &[Option<Assignment>],
        non_recursive_call: bool,
    ) -> Watcher {
        let max_pointer = std::cmp::max(self.watch_ptr[0], self.watch_ptr[1]);

        // incrementar o ponteiro faria ele ultrapassar o array
        // vai retorna o literal que sobrou para ser propagado ou retornar conflito se o último literal discorda do modelo
        if max_pointer == self.literals.len() - 1 {
            let not_watched: Literal = self.point((pointer_to_lit + 1) % 2).unwrap();
            match self.model_agreement(model, not_watched) {
                Some(true) => panic!("Devia ter retornado satisfied antes de chegar aqui"),
                Some(false) => Watcher::Conflict(not_watched),
                None => Watcher::Unit(not_watched),
            }
        } else {
            // incrementa o ponteiro?
            // a grande sacanagem é que você pode ter que chamar next n vezes recursivamente
            // mas se ela for propagar unidade o ponteiro não se move nem uma vez
            // meu deus que detalhe mais cretino
            let checkpoint = self.watch_ptr[pointer_to_lit];
            self.watch_ptr[pointer_to_lit] = max_pointer + 1;
            let candidate = self.point(pointer_to_lit).unwrap();
            match self.model_agreement(model, candidate) {
                Some(true) => Watcher::Satisfied(candidate),
                Some(false) => {
                    let watched = self.next(pointer_to_lit, model, false);
                    if non_recursive_call {
                        if let Watcher::Unit(_) = &watched {
                            self.watch_ptr[pointer_to_lit] = checkpoint;
                        } else if let Watcher::Conflict(_) = &watched {
                            self.watch_ptr[pointer_to_lit] = checkpoint;
                        }
                    }
                    watched
                }
                None => Watcher::Watched(candidate),
            }
        }
    }

    // Some(true) se o modelo concorda, Some(false) se ele discorda, None se ele não acha nada
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

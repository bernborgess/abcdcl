use std::collections::HashSet;
use std::fmt;
pub enum Watcher {
    Unit(Literal),
    NewWatched(Literal),
    Conflict,
}

use Watcher::*;

use super::{assignment::Assignment, literal::Literal};

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    watch_ptr: [usize; 2],
    status: ClauseStates,
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
            status: ClauseStates::Unresolved,
        }
    }

    pub fn new_vec(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| v.iter().map(|x| Literal::new(&x)).collect())
            .map(Clause::new)
            .collect()
    }

    pub fn watch(&mut self, lit: Literal, model: &[Option<Assignment>]) -> Watcher {
        if let ClauseStates::Satisfied(lit) = self.status {
            Watcher::NewWatched(lit)
        } else {
            if self.literals.len() == 1 {
                return Unit(lit);
            }
            let ind: usize = if self.point(0) == lit {
                //seleciona o ponteiro que vai ser movido
                0
            } else if self.point(1) == lit {
                1
            } else {
                panic!("There's only 2 pointers")
            };

            //move o ponteiro
            let mut status: Watcher = self.next(ind);

            //se não encontrar uma cláusula unitária, checa o novo literal vigiado
            //se o novo literal vigiado for falseado pelo modelo, move o ponteiro de novo
            //se o novo literal vigiado for satisfeito pelo modelo, para de vigiar a cláusula
            let mut sat_or_unsat = self.satisfied_or_falsified(&status, model);
            while let Some(false) = &sat_or_unsat {
                status = self.next(ind);
                sat_or_unsat = self.satisfied_or_falsified(&status, model);
            }

            match &status{
                &Watcher::Unit(to_prop) => self.status = ClauseStates::Unit(to_prop),
                &Watcher::NewWatched(new_lit) => {
                    match sat_or_unsat{
                        Some(true) => self.status = ClauseStates::Satisfied(new_lit),
                        Some(false) => panic!("This should be impossible. The pointer should move until this turn into Unit or find a non-falsified literal"),
                        None => self.status = ClauseStates::Unresolved,
                    }
                }
                Watcher::Conflict => panic!("Should be dead"),
            }
            status
        }
    }

    //Some(true) se satisfeito, Some(false) se falseado, None se não atribuído ou se é Unidade ou Conflito
    fn satisfied_or_falsified(
        &self,
        status: &Watcher,
        model: &[Option<Assignment>],
    ) -> Option<bool> {
        match status {
            Watcher::Unit(_) => None,
            Watcher::Conflict => None,
            &Watcher::NewWatched(to) => {
                model[to.variable].map(|assignment| assignment.polarity != to.polarity)
            }
        }
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> Literal {
        self.literals[self.watch_ptr[i]]
    }

    fn next(&mut self, i: usize) -> Watcher {
        // Se o outro ponteiro já tiver explodido, retorna conflito
        if self.watch_ptr[(i + 1) % 2] >= self.literals.len() {
            return Conflict; //Isso deve ser código morto, mas vou deixar essa linha pra detectar bug
        }
        let max_pointer = std::cmp::max(self.watch_ptr[0], self.watch_ptr[1]);
        // if self.watch_ptr[0] < self.watch_ptr[1] {
        //     self.watch_ptr[1]
        // } else {
        //     self.watch_ptr[0]
        // };
        //nova posição para onde o ponteiro i vai apontar
        self.watch_ptr[i] = max_pointer + 1;

        // caso ponteiro ultrapasse o array, retorna o literal que sobrou no outro ponteiro para ser propagado
        if self.watch_ptr[i] == self.literals.len() {
            self.status = ClauseStates::Unit(self.point((i + 1) % 2));
            Unit(self.point((i + 1) % 2))
        } else {
            NewWatched(self.point(i)) // retorna o novo literal vigiado
        }
    }

    pub fn resolution(&self, other: &Clause, pivot: Literal) -> Clause {
        let mut first: HashSet<Literal> = self.literals.iter().cloned().collect();
        let second: HashSet<Literal> = other.literals.iter().cloned().collect();
        first.extend(&second);
        first.remove(&pivot);
        first.remove(&pivot.negate());
        let data: Vec<Literal> = first.into_iter().collect();
        Clause {
            literals: data,
            watch_ptr: [0, 1],
            status: ClauseStates::Unresolved,
        }
    }
}

#[derive(Clone, Debug)]
enum ClauseStates {
    Satisfied(Literal),
    Falsified(Literal),
    Unit(Literal),
    Unresolved,
}

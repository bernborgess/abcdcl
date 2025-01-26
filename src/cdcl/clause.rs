use std::collections::HashSet;
use std::fmt;
pub enum Watcher {
    OnlyOneRemaining(Literal),
    Watched(Literal),
    AlreadyWatched,
    Conflict,
}

use Watcher::*;

use super::{assignment::Assignment, literal::Literal};

#[derive(Clone)]
pub struct Clause {
    pub literals: Vec<Literal>,
    watch_ptr: [usize; 2],
    satisfied_on_dl: Option<usize>,
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
            satisfied_on_dl: None,
        }
    }

    pub fn new_vec(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| v.iter().map(|x| Literal::new(&x)).collect())
            .map(Clause::new)
            .collect()
    }

    pub fn watch(
        &mut self,
        lit: Literal,
        model: &[Option<Assignment>],
        decision_level: usize,
    ) -> Watcher {
        if let Some(sats) = self.satisfied_on_dl {
            if sats <= decision_level {
                return AlreadyWatched;
            }
            self.satisfied_on_dl = None;
        }
        if self.literals.len() == 1 {
            //devia ser código morto
            return OnlyOneRemaining(lit);
        }
        // Um dos ponteiros está estourado, cláusula já foi vigiada
        let opt_ind: Option<usize> = if self.point(0).is_none() || self.point(1).is_none() {
            None
        }
        //seleciona o ponteiro que vai ser movido
        else if self.point(0).unwrap() == lit {
            Some(0)
        } else if self.point(1).unwrap() == lit {
            Some(1)
        } else {
            //se nenhum dos ponteiros aponta para lit, essa cláusula já foi vigiado e lit está para trás
            None
        };
        if let Some(ind) = opt_ind {
            //move o ponteiro
            let mut status: Watcher = self.next(ind);

            //se não encontrar uma cláusula OnlyOneRemaining, checa o novo literal vigiado
            //se o novo literal vigiado for falseado pelo modelo, move o ponteiro de novo
            //se o novo literal vigiado for satisfeito pelo modelo, para de vigiar a cláusula
            let mut sat_or_unsat = self.satisfied_or_falsified(&status, model);
            while let Some(false) = &sat_or_unsat {
                status = self.next(ind);
                sat_or_unsat = self.satisfied_or_falsified(&status, model);
            }

            match &status{
                Watcher::OnlyOneRemaining(_) => (),
                Watcher::Watched(_) => {
                    match sat_or_unsat{
                        Some(true) => self.satisfied_on_dl = Some(decision_level),
                        Some(false) => panic!("This should be impossible. The pointer should move until this turn into OnlyOneRemaining or find a non-falsified literal"),
                        None => self.satisfied_on_dl = None,
                    }
                }
                _ => panic!("Should be dead"),
            }
            status
        } else {
            Watcher::AlreadyWatched
        }
    }

    //Some(true) se satisfeito, Some(false) se falseado, None se não atribuído ou se é Unidade ou Conflito
    fn satisfied_or_falsified(
        &self,
        status: &Watcher,
        model: &[Option<Assignment>],
    ) -> Option<bool> {
        match status {
            &Watcher::Watched(to) => {
                model[to.variable].map(|assignment| assignment.polarity == to.polarity)
            }
            _ => None,
        }
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> Option<Literal> {
        self.literals.get(self.watch_ptr[i]).copied()
    }

    fn next(&mut self, i: usize) -> Watcher {
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
            OnlyOneRemaining(self.point((i + 1) % 2).unwrap())
        } else {
            Watched(self.point(i).unwrap()) // retorna o novo literal vigiado
        }
    }

    pub fn resolution(&self, other: &Clause, pivot: Literal) -> Clause {
        let mut first: Vec<Literal> = self
            .literals
            .iter()
            .filter(|&x| x != &pivot)
            .cloned()
            .collect();
        let second: Vec<Literal> = other.literals.clone();
        println!("Resolving on pivot {:?}: ", &pivot);
        println!("{:?}", &self.literals);
        println!("{:?}", &second);
        let mut seen: HashSet<Literal> = first.iter().cloned().collect();
        seen.remove(&pivot);
        seen.remove(&pivot.negate());

        for &item in second.iter() {
            //só insere se o item não está no conjunto e não é o pivo
            if (!seen.contains(&item)) && (item.variable != pivot.variable) {
                first.push(item);
            }
        }
        println!("Result:");
        println!("{:?}\n", &first);
        Clause {
            literals: first,
            watch_ptr: [0, 1],
            satisfied_on_dl: None,
        }
    }

    pub fn set_satisfied(&mut self, decision_level: usize) {
        self.satisfied_on_dl = Some(decision_level);
    }
}

#[derive(Clone, Debug)]
enum ClauseStates {
    Satisfied(Literal),
    Unresolved,
}

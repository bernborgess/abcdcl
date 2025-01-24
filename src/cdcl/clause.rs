use std::fmt;

pub enum Watcher {
    Unit(i64),
    //AlreadyWatched(i64),
    NewWatched(i64),
    Conflict,
}

use Watcher::*;

use super::utils::get_sign;

/*impl Watcher{
    fn unwrap(&self)->i64{
        match self{
            &Unit(v) => v,
            &WatchedFromTo(from,to) => (from,to),
            Conflict => panic!("Unwrap on conflict")
        }
    }
}*/

#[derive(Clone)]
pub struct Clause {
    pub data: Vec<i64>,
    watch_ptr: [usize; 2],
    status: ClauseStates,
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Define how you want your struct to be printed
        for (i, lit) in self.data.iter().enumerate() {
            if (self.watch_ptr[0] == i) || (self.watch_ptr[1] == i) {
                write!(f, "•");
            }
            write!(f, "{:?},", lit);
        }
        writeln!(f, "");
        Ok(())
    }
}

impl Clause {
    pub fn new(arr: Vec<Vec<i64>>) -> Vec<Clause> {
        arr.into_iter()
            .map(|v| Clause {
                data: v,
                watch_ptr: [0, 1],
                status: ClauseStates::Unresolved,
            })
            .collect()
    }

    pub fn watch(&mut self, lit: i64, model: &[Option<bool>]) -> Watcher {
        if let ClauseStates::Satisfied(lit) = self.status {
            Watcher::NewWatched(lit)
        } else {
            if self.data.len() == 1 {
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
    fn satisfied_or_falsified(&self, status: &Watcher, model: &[Option<bool>]) -> Option<bool> {
        match status {
            Watcher::Unit(_) => None,
            Watcher::Conflict => None,
            &Watcher::NewWatched(to) => {
                let polarity = get_sign(to);
                model[to.unsigned_abs() as usize].map(|assignment| assignment == polarity)
            }
        }
    }

    //retorna o valor apontado pelo ponteiro i
    fn point(&self, i: usize) -> i64 {
        self.data[self.watch_ptr[i]]
    }

    fn next(&mut self, i: usize) -> Watcher {
        // Se o outro ponteiro já tiver explodido, retorna conflito
        if self.watch_ptr[(i + 1) % 2] >= self.data.len() {
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
        if self.watch_ptr[i] == self.data.len() {
            self.status = ClauseStates::Unit(self.point((i + 1) % 2));
            Unit(self.point((i + 1) % 2))
        } else {
            NewWatched(self.point(i)) // retorna o novo literal vigiado
        }
    }
}

#[derive(Clone, Debug)]
enum ClauseStates {
    Satisfied(i64),
    Falsified(i64),
    Unit(i64),
    Unresolved,
}

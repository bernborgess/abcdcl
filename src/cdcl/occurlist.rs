use std::mem;

//Some(true) se satisfeito, Some(false) se falseado, None se não atribuído ou se é Unidade ou Conflito
#[derive(Debug, Default)]
pub struct OccurLists {
    pub positive: Vec<Vec<usize>>, // positive[k] contém os índices das cláusulas que têm o literal +k vigiado
    pub negative: Vec<Vec<usize>>, // negative[k] contém os índices das cláusulas que têm o literal -k vigiado
}

impl OccurLists {
    pub fn new(n: usize) -> OccurLists {
        OccurLists {
            positive: vec![Vec::new(); n + 1], //aloco 1 espaço a mais para garantir indexação em base 1
            negative: vec![Vec::new(); n + 1],
        }
    }

    pub fn take(&mut self, lit: i64) -> Vec<usize> {
        if lit < 0 {
            mem::take(&mut self.negative[lit.unsigned_abs() as usize])
        } else {
            mem::take(&mut self.positive[lit.unsigned_abs() as usize])
        }
    }

    pub fn give_to(&mut self, clause_lists: Vec<usize>, lit: i64) {
        if lit < 0 {
            self.negative[lit.unsigned_abs() as usize] = clause_lists;
        } else {
            self.positive[lit.unsigned_abs() as usize] = clause_lists;
        }
    }

    pub fn get(&self, lit: i64) -> &Vec<usize> {
        if lit < 0 {
            &self.negative[lit.unsigned_abs() as usize]
        } else {
            &self.positive[lit.unsigned_abs() as usize]
        }
    }

    pub fn get_mut(&mut self, lit: i64) -> &mut Vec<usize> {
        if lit < 0 {
            &mut self.negative[lit.unsigned_abs() as usize]
        } else {
            &mut self.positive[lit.unsigned_abs() as usize]
        }
    }

    pub fn add_clause_to_lit(&mut self, clause: usize, lit: i64) {
        self.get_mut(lit).push(clause);
    }

    fn remove_clauses_from_lit(&mut self, clauses: &Vec<usize>, lit: i64) {
        let lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list
            .drain(..)
            .filter(|x| !clauses.contains(x))
            .collect();
    }

    fn remove_clause_from_lit(&mut self, clause: usize, lit: i64) {
        let lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list.drain(..).filter(|&x| clause != x).collect();
    }
}

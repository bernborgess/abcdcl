use std::mem;

use super::literal::Literal;

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

    pub fn take(&mut self, lit: Literal) -> Vec<usize> {
        if lit.polarity {
            mem::take(&mut self.positive[lit.variable])
        } else {
            mem::take(&mut self.negative[lit.variable])
        }
    }

    pub fn give_to(&mut self, clause_lists: Vec<usize>, lit: Literal) {
        if lit.polarity {
            self.positive[lit.variable] = clause_lists;
        } else {
            self.negative[lit.variable] = clause_lists;
        }
    }

    pub fn get(&self, lit: Literal) -> &Vec<usize> {
        if lit.polarity {
            &self.positive[lit.variable]
        } else {
            &self.negative[lit.variable]
        }
    }

    pub fn get_mut(&mut self, lit: Literal) -> &mut Vec<usize> {
        if lit.polarity {
            &mut self.positive[lit.variable]
        } else {
            &mut self.negative[lit.variable]
        }
    }

    pub fn add_clause_to_lit(&mut self, clause_id: usize, lit: Literal) {
        self.get_mut(lit).push(clause_id);
    }

    fn remove_clauses_from_lit(&mut self, clauses: &Vec<usize>, lit: Literal) {
        let lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list
            .drain(..)
            .filter(|x| !clauses.contains(x))
            .collect();
    }

    fn remove_clause_from_lit(&mut self, clause: usize, lit: Literal) {
        let lit_occur_list: &mut Vec<usize> = self.get_mut(lit);
        *lit_occur_list = lit_occur_list.drain(..).filter(|&x| clause != x).collect();
    }
}

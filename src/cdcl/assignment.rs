#[derive(Clone, Copy, Debug)]
pub struct Assignment {
    pub polarity: bool,
    pub antecedent: Option<usize>, //Se Some(v); v é o índice da cláusula antecedente
    pub dl: usize,
}

impl Assignment {
    pub fn new(polarity: bool, dl: usize, antecedent: Option<usize>) -> Assignment {
        Assignment {
            polarity,
            antecedent,
            dl,
        }
    }
}

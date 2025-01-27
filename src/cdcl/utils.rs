use super::assignment::Assignment;
use super::clause::Clause;
pub fn print_model(model: &[Option<Assignment>]) {
    eprintln!("current model: ");
    for (i, m) in model.iter().enumerate().skip(1) {
        if let Some(asgnmt) = m {
            if asgnmt.polarity {
                eprint!("{i},");
            } else {
                eprint!("-{i},");
            }
        }
    }
    eprintln!();
}

pub fn remove_clauses_from_lit(to_remove: &Vec<usize>, occur_list_of_lit: &mut Vec<usize>) {
    *occur_list_of_lit = occur_list_of_lit
        .drain(..)
        .filter(|x| !to_remove.contains(x))
        .collect();
}

pub fn print_decision_levels(clause: &Clause, model: &[Option<Assignment>]) {
    for i in clause.literals.iter() {
        if !i.polarity {
            print!("¬")
        }
        print!(
            "p{:?}({:?}); ",
            i.variable,
            model[i.variable]
                .unwrap_or({
                    println!(
                        "Mas que porra? Se não tá no modelo, como tá na cláusula de conflito?"
                    );
                    println!("A dita cuja: {:?}", clause);
                    println!("O modelo:");
                    println!("{:?}", model);
                    Assignment {
                        dl: 6969,
                        polarity: true,
                        antecedent: None,
                    }
                })
                .dl
        );
    }
    println!();
}

pub fn remove_duplicates<T: Ord>(v: &mut Vec<T>) {
    v.sort();
    v.dedup();
}

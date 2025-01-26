use super::assignment::Assignment;
pub fn print_model(model: &[Option<Assignment>]) {
    print!("current model: ");
    for (i, m) in model.iter().enumerate().skip(1) {
        if let Some(asgnmt) = m {
            if asgnmt.polarity {
                print!("{i},");
            } else {
                print!("-{i},");
            }
        }
    }
    println!();
}

pub fn remove_clauses_from_lit(to_remove: &Vec<usize>, occur_list_of_lit: &mut Vec<usize>) {
    *occur_list_of_lit = occur_list_of_lit
        .drain(..)
        .filter(|x| !to_remove.contains(x))
        .collect();
}

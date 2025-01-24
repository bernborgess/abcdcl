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

use std::cmp::Ordering;

pub fn get_sign(lit: i64) -> bool {
    match lit.cmp(&0) {
        Ordering::Greater => true,
        Ordering::Less => false,
        Ordering::Equal => panic!("0 is not a literal"),
    }
}

pub fn print_model(model: &[Option<bool>]) {
    print!("current model: ");
    for (i, m) in model.iter().enumerate().skip(1) {
        match m {
            Some(true) => print!("{i},"),
            Some(false) => print!("-{i},"),
            None => (),
        }
    }
    println!();
}

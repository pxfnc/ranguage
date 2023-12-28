mod lambda;
mod nom_ext;
mod typed_lambda;

use nom::error::convert_error;
use nom::Finish as _;
use std::io::Write as _;

fn main() -> std::io::Result<()> {
    let mut stdout = std::io::stdout();
    let stdin = std::io::stdin();
    loop {
        let mut buff = String::new();
        print!("input lambda expr \n> ");
        stdout.flush()?;
        stdin.read_line(&mut buff)?;
        let i = buff.as_str().trim();
        println!("input -> {:?}", i);
        match typed_lambda::parse_lamnb(i).finish() {
            Ok((rest, lambda)) => println!(
                "result -> {}\nast -> {:?}\nrest -> {:?}",
                lambda, lambda, rest
            ),
            Err(e) => println!("{}", convert_error(i, e)),
        }
        print!("\n\n\n");
    }
}

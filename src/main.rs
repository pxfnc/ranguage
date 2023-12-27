use std::io::Write as _;

mod lambda;

use lambda::parse_lambda;
use nom::error::convert_error;
use nom::Finish as _;

fn main() -> std::io::Result<()> {
    let mut stdout = std::io::stdout();
    let stdin = std::io::stdin();
    loop {
        let mut buff = String::new();
        print!("input lambda expr \n> ");
        stdout.flush()?;
        stdin.read_line(&mut buff)?;
        let i = buff.trim();
        println!("input -> {}", i);
        match parse_lambda(i).finish() {
            Ok((rest, lambda)) => println!("result -> {}\nrest -> {:?}", lambda, rest),
            Err(e) => println!("{}", convert_error(i, e)),
        }
        print!("\n\n\n");
    }
}

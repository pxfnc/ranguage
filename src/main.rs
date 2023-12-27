use std::io::Write as _;

use nom::branch::alt;
use nom::character::complete::{alpha1, char, satisfy, space0};
use nom::error::{convert_error, VerboseError};
use nom::sequence::delimited;
use nom::{Finish as _, IResult};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Lambda {
    Var(char),
    Abs(String, Box<Lambda>),
    App(Box<Lambda>, Box<Lambda>),
}

impl std::fmt::Display for Lambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lambda::Var(c) => write!(f, "{}", c.to_string()),
            Lambda::Abs(s, lambda) => write!(f, "λ{}.{}", s, lambda),
            Lambda::App(lambda1, lambda2) => match lambda2.as_ref() {
                app @ Lambda::App(..) => return write!(f, "{}({})", lambda1, app),
                _ => write!(f, "{}{}", lambda1, lambda2),
            },
        }
    }
}

#[allow(dead_code)]
fn var(c: char) -> Lambda {
    Lambda::Var(c)
}

fn abs(s: &str, lambda: Lambda) -> Lambda {
    Lambda::Abs(s.to_string(), Box::new(lambda))
}

fn app(lambda1: Lambda, lambda2: Lambda) -> Lambda {
    Lambda::App(Box::new(lambda1), Box::new(lambda2))
}

fn parse_var(input: &str) -> IResult<&str, Lambda, VerboseError<&str>> {
    let (input, var) = satisfy(|c| c.is_ascii_alphabetic())(input)?;
    Ok((input, Lambda::Var(var)))
}

fn parse_abs(input: &str) -> IResult<&str, Lambda, VerboseError<&str>> {
    let (input, _) = char('\\')(input)?;
    let (input, var) = alpha1(input)?;
    let (input, _) = char('.')(input)?;
    let (input, lambda) = parse_lambda(input)?;
    Ok((input, abs(var, lambda)))
}

fn parse_lambda(input: &str) -> IResult<&str, Lambda, VerboseError<&str>> {
    fn parse_var_or_abs(input: &str) -> IResult<&str, Lambda, VerboseError<&str>> {
        alt((parse_var, parse_abs))(input)
    }

    fn parse_expr(input: &str) -> IResult<&str, Lambda, VerboseError<&str>> {
        alt((
            delimited(char('('), parse_lambda, char(')')),
            parse_var_or_abs,
        ))(input)
    }
    fn parse_op(input: &str) -> IResult<&str, fn(Lambda, Lambda) -> Lambda, VerboseError<&str>> {
        let (input, _) = space0(input)?;
        Ok((input, app))
    }

    chainl1(parse_expr, parse_op)(input)
}

fn chainl1<'a, T>(
    mut term: impl FnMut(&'a str) -> IResult<&'a str, T, VerboseError<&'a str>>,
    mut binary_op: impl FnMut(&'a str) -> IResult<&'a str, fn(T, T) -> T, VerboseError<&'a str>>,
) -> impl FnMut(&'a str) -> IResult<&'a str, T, VerboseError<&'a str>> {
    move |input: &str| {
        let (mut input, mut lhs) = term(input)?;
        while let Ok((rest, (op, rhs))) = binary_op(input)
            .and_then(|(input, op)| term(input).map(|(input, rhs)| (input, (op, rhs))))
        {
            lhs = op(lhs, rhs);
            input = rest;
        }

        Ok((input, lhs))
    }
}

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

#[cfg(test)]
mod tests {

    use std::str::FromStr;

    use nom::combinator::map_res;

    use super::*;
    #[test]
    fn test_parse_lambda() {
        assert_eq!(
            parse_lambda("abc"),
            Ok(("", app(app(var('a'), var('b')), var('c'))))
        );
        assert_eq!(parse_lambda("x"), Ok(("", var('x'))));
        assert_eq!(parse_lambda("x"), Ok(("", var('x'))));
        assert_eq!(parse_lambda("\\x.x"), Ok(("", abs("x", var('x')))));
        assert_eq!(
            parse_abs("\\x.\\y.x"),
            Ok(("", abs("x", abs("y", var('x')))))
        );
        assert_eq!(
            parse_lambda("(\\x.x)y"),
            Ok(("", app(abs("x", var('x')), var('y'))))
        );
        assert_eq!(
            parse_lambda("abc"),
            Ok(("", app(app(var('a'), var('b')), var('c'))))
        );

        assert_eq!(
            parse_lambda("a(bc)"),
            Ok(("", app(var('a'), app(var('b'), var('c')))))
        );
    }

    #[test]
    fn test_chainl1() {
        let mut parser = chainl1(map_res(alpha1, String::from_str), |ipt| {
            let (ipt, _) = char('+')(ipt)?;
            Ok((ipt, |fst: String, snd: String| format!("({}+{})", fst, snd)))
        });
        assert_eq!(parser("a"), Ok(("", "a".to_string())));
        assert_eq!(parser("a+b+c"), Ok(("", "((a+b)+c)".to_string())));
    }
}

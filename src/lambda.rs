#![allow(dead_code)]
use nom::branch::alt;
use nom::character::complete::{char, satisfy, space0};
use nom::combinator::{fail, value};
use nom::error::ParseError;
use nom::sequence::delimited;
use nom::IResult;
use nom::Parser as _;

use crate::nom_ext;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lambda {
    Var(char),
    Abs(String, Box<Lambda>),
    App(Box<Lambda>, Box<Lambda>),
}

impl std::fmt::Display for Lambda {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Lambda::Var(c) => write!(f, "{}", c),
            Lambda::Abs(s, lambda) => write!(f, "λ{}.{}", s, lambda),
            Lambda::App(lambda1, lambda2) => match lambda2.as_ref() {
                app @ Lambda::App(..) => write!(f, "{}({})", lambda1, app),
                _ => write!(f, "{}{}", lambda1, lambda2),
            },
        }
    }
}

#[allow(dead_code)]
fn var(c: char) -> Lambda {
    Lambda::Var(c)
}

fn abs(s: char, lambda: Lambda) -> Lambda {
    Lambda::Abs(s.to_string(), Box::new(lambda))
}

fn app(lambda1: Lambda, lambda2: Lambda) -> Lambda {
    Lambda::App(Box::new(lambda1), Box::new(lambda2))
}

fn parse_var<'a, Error: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lambda, Error> {
    let (input, var) = satisfy(|c| c.is_ascii_alphabetic())(input)?;
    Ok((input, Lambda::Var(var)))
}

fn parse_abs<'a, Error>(input: &'a str) -> IResult<&'a str, Lambda, Error>
where
    Error: ParseError<&'a str>,
{
    let (input, _) = char('\\')(input)?;
    if let (input, Lambda::Var(var)) = parse_var(input)? {
        let (input, _) = char('.')(input)?;
        let (input, lambda) = parse_lambda(input)?;
        Ok((input, abs(var, lambda)))
    } else {
        fail(input)
    }
}

fn parse_lambda<'a, Error>(input: &'a str) -> IResult<&'a str, Lambda, Error>
where
    Error: ParseError<&'a str>,
{
    let parse_var_or_abs = alt((parse_var, parse_abs));

    let parse_expr = alt((
        delimited(char('('), parse_lambda, char(')')),
        parse_var_or_abs,
    ));

    let parse_op = value(app, space0);
    nom_ext::chainl1(parse_expr, parse_op).parse(input)
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn test_parse_lambda() {
        assert_eq!(
            parse_lambda::<()>("abc"),
            Ok(("", app(app(var('a'), var('b')), var('c'))))
        );
        assert_eq!(parse_lambda::<()>("x"), Ok(("", var('x'))));
        assert_eq!(parse_lambda::<()>("x"), Ok(("", var('x'))));
        assert_eq!(parse_lambda::<()>("\\x.x"), Ok(("", abs('x', var('x')))));
        assert_eq!(
            parse_abs::<()>("\\x.\\y.x"),
            Ok(("", abs('x', abs('y', var('x')))))
        );
        assert_eq!(
            parse_lambda::<()>("(\\x.x)y"),
            Ok(("", app(abs('x', var('x')), var('y'))))
        );
        assert_eq!(
            parse_lambda::<()>("abc"),
            Ok(("", app(app(var('a'), var('b')), var('c'))))
        );

        assert_eq!(
            parse_lambda::<()>("a(bc)"),
            Ok(("", app(var('a'), app(var('b'), var('c')))))
        );
    }
}

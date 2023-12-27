use nom::branch::alt;
use nom::character::complete::{char, satisfy, space0};
use nom::combinator::{fail, value};
use nom::error::ParseError;
use nom::sequence::delimited;
use nom::IResult;

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
pub fn var(c: char) -> Lambda {
    Lambda::Var(c)
}

pub fn abs(s: char, lambda: Lambda) -> Lambda {
    Lambda::Abs(s.to_string(), Box::new(lambda))
}

pub fn app(lambda1: Lambda, lambda2: Lambda) -> Lambda {
    Lambda::App(Box::new(lambda1), Box::new(lambda2))
}

pub fn parse_var<'a, Error: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Lambda, Error> {
    let (input, var) = satisfy(|c| c.is_ascii_alphabetic())(input)?;
    Ok((input, Lambda::Var(var)))
}

pub fn parse_abs<'a, Error>(input: &'a str) -> IResult<&'a str, Lambda, Error>
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

pub fn parse_lambda<'a, Error>(input: &'a str) -> IResult<&'a str, Lambda, Error>
where
    Error: ParseError<&'a str>,
{
    let parse_var_or_abs = alt((parse_var, parse_abs));

    let parse_expr = alt((
        delimited(char('('), parse_lambda, char(')')),
        parse_var_or_abs,
    ));

    let parse_op = value(app, space0);
    chainl1(parse_expr, parse_op)(input)
}

pub fn chainl1<'a, T, Op, Error>(
    mut term: impl FnMut(&'a str) -> IResult<&'a str, T, Error>,
    mut binary_op: impl FnMut(&'a str) -> IResult<&'a str, Op, Error>,
) -> impl FnMut(&'a str) -> IResult<&'a str, T, Error>
where
    Error: ParseError<&'a str>,
    Op: Fn(T, T) -> T,
{
    move |input: &'a str| {
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

#[cfg(test)]
mod tests {

    use std::str::FromStr;

    use nom::{character::complete::alpha1, combinator::map_res};

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

    #[test]
    fn test_chainl1() {
        let mut parser = chainl1::<_, _, ()>(map_res(alpha1, String::from_str), |ipt| {
            let (ipt, _) = char('+')(ipt)?;
            Ok((ipt, |fst: String, snd: String| format!("({}+{})", fst, snd)))
        });
        assert_eq!(parser("a"), Ok(("", "a".to_string())));
        assert_eq!(parser("a+b+c"), Ok(("", "((a+b)+c)".to_string())));
    }
}

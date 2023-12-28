#![allow(dead_code)]

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, char, digit1, space0, space1};
use nom::combinator::{self, cut, flat_map, map, map_opt, peek, value, verify};
use nom::error::{context, ContextError, ParseError};
use nom::sequence::{delimited, pair, preceded, terminated, tuple};
use nom::{IResult, Parser};

use crate::nom_ext::chainl1;

/// Lambda + Nat + Bool
///
/// operator order
///
/// infixl 3 App
/// infixl 2 Mul
/// infixl 1 Add
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LamNB {
    Nat(u32),
    Bool(bool),
    Var(String),
    IfElse(Box<LamNB>, Box<LamNB>, Box<LamNB>),
    Add(Box<LamNB>, Box<LamNB>),
    Mul(Box<LamNB>, Box<LamNB>),
    Abs(String, Box<LamNB>),
    App(Box<LamNB>, Box<LamNB>),
}

const KEYWORDS: [&str; 5] = ["if", "then", "else", "true", "false"];

use LamNB::*;

pub fn nat(n: u32) -> LamNB {
    Nat(n)
}

pub fn bool(b: bool) -> LamNB {
    Bool(b)
}

pub fn var(s: impl Into<String>) -> LamNB {
    Var(s.into())
}

pub fn if_else(cond: LamNB, tr: LamNB, fls: LamNB) -> LamNB {
    IfElse(Box::new(cond), Box::new(tr), Box::new(fls))
}

pub fn add(lhs: LamNB, rhs: LamNB) -> LamNB {
    Add(Box::new(lhs), Box::new(rhs))
}

pub fn mul(lhs: LamNB, rhs: LamNB) -> LamNB {
    Mul(Box::new(lhs), Box::new(rhs))
}

pub fn abs(s: impl Into<String>, lambda: LamNB) -> LamNB {
    Abs(s.into(), Box::new(lambda))
}

pub fn app(lambda1: LamNB, lambda2: LamNB) -> LamNB {
    App(Box::new(lambda1), Box::new(lambda2))
}

impl std::fmt::Display for LamNB {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Nat(n) => write!(f, "{n}"),
            Bool(b) => write!(f, "{b}"),
            Var(c) => write!(f, "{c}"),
            IfElse(cond, tr, fls) => write!(f, "if {cond} then {tr} else {fls}"),
            Add(lhs, rhs) => write!(f, "{} + {}", lhs, rhs),
            Mul(lhs, rhs) => write!(f, "{lhs} × {rhs}"),
            Abs(s, lambda) => write!(f, "λ{}.{}", s, lambda),
            App(lambda1, lambda2) => match lambda2.as_ref() {
                app @ App(..) => write!(f, "{} ({})", lambda1, app),
                _ => write!(f, "{} {}", lambda1, lambda2),
            },
        }
    }
}

fn parse_num<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "num",
        map_opt(digit1, |s: &'a str| (s.parse::<u32>().ok()).map(Nat)),
    )(input)
}

fn parse_bool<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "bool",
        alt((
            combinator::value(Bool(true), nom::bytes::complete::tag("true")),
            combinator::value(Bool(false), nom::bytes::complete::tag("false")),
        )),
    )(input)
}

fn parse_var<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "var",
        map_opt(alpha1, |s: &str| {
            Some(s).filter(|s| !KEYWORDS.contains(s)).map(var)
        }),
    )(input)
}

fn parse_abs<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "abs",
        map(
            pair(
                delimited(
                    terminated(char('\\'), space0),
                    map_opt(terminated(parse_var, space0), |v| match v {
                        Var(c) => Some(c),
                        _ => None,
                    }),
                    terminated(char('.'), space0),
                ),
                cut(parse_lamnb),
            ),
            |(var, expr)| abs(var, expr),
        ),
    )(input)
}

fn parse_prim<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context("prim", alt((parse_abs, parse_num, parse_bool, parse_var)))(input)
}

fn parse_app<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context("app", chainl1(parse_prim, value(app, space1))).parse(input)
}

fn parse_mul<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "mul",
        chainl1(
            parse_app,
            combinator::value(mul, delimited(space0, char('*'), space0)),
        ),
    )
    .parse(input)
}

fn parse_add<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "add",
        chainl1(parse_mul, value(add, delimited(space0, char('+'), space0))),
    )
    .parse(input)
}

fn parse_if_else<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "ifelse",
        preceded(
            tuple((tag("if"), space1)),
            cut(flat_map(
                terminated(parse_add, tuple((space1, tag("then"), space1))),
                |cond| {
                    cut(flat_map(
                        terminated(parse_add, tuple((space1, tag("else"), space1))),
                        move |b| {
                            let cond = cond.clone();
                            cut(map(parse_lamnb, move |c| {
                                if_else(cond.clone(), b.clone(), c)
                            }))
                        },
                    ))
                },
            )),
        ),
    )(input)
}

pub fn parse_lamnb<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "lamnb",
        delimited(
            space0,
            alt((
                preceded(
                    verify(peek(alpha1), |s: &str| s == "if"),
                    cut(parse_if_else),
                ),
                parse_add,
            )),
            space0,
        ),
    )(input)
}

#[cfg(test)]
mod test {

    use nom::error::VerboseError;
    use nom::Finish as _;

    use super::*;

    fn run<'a, O>(
        mut p: impl Parser<&'a str, O, VerboseError<&'a str>>,
        ipt: &'a str,
    ) -> Result<(&'a str, O), String>
where {
        p.parse(ipt)
            .finish()
            .map_err(|e| nom::error::convert_error(ipt, e))
    }

    #[test]
    fn test_parse() {
        assert_eq!(run(parse_lamnb, "1"), Ok(("", nat(1))));
        assert_eq!(run(parse_lamnb, "123"), Ok(("", nat(123))));
        assert_eq!(run(parse_lamnb, "    v  "), Ok(("", var("v".to_string()))));
        assert_eq!(
            run(parse_lamnb, "  1 +   2 + 3 "),
            Ok(("", add(add(nat(1), nat(2)), nat(3))))
        );
        assert_eq!(
            run(parse_lamnb, "1*2+3"),
            Ok(("", add(mul(nat(1), nat(2)), nat(3))))
        );
        assert_eq!(
            run(parse_lamnb, "1 +2   *3"),
            Ok(("", add(nat(1), mul(nat(2), nat(3)))))
        );

        assert_eq!(run(parse_lamnb, "\\x.x"), Ok(("", abs("x", var("x")))));
        assert_eq!(
            run(parse_lamnb, "  \\  x .  x  "),
            Ok(("", abs("x", var("x"))))
        );

        assert_eq!(
            run(parse_lamnb, "\\x.x+2"),
            Ok(("", abs("x", add(var("x"), nat(2)))))
        );

        assert_eq!(
            run(parse_lamnb, "f \\x.f x"),
            Ok(("", app(var("f"), abs("x", app(var("f"), var("x"))))))
        );

        assert_eq!(run(parse_lamnb, "iff"), Ok(("", var("iff"))));
        assert_eq!(
            run(parse_lamnb, "if cond then 1 else \\x.x"),
            Ok(("", if_else(var("cond"), nat(1), abs("x", var("x")))))
        );
        assert_eq!(
            run(parse_lamnb, "\\cond. if cond then 1 else \\x.x"),
            Ok((
                "",
                abs("cond", if_else(var("cond"), nat(1), abs("x", var("x"))))
            ))
        );

        assert_eq!(
            run(parse_lamnb, "if 1 then 2 else if 3 then 4 else 5"),
            Ok(("", if_else(nat(1), nat(2), if_else(nat(3), nat(4), nat(5)))))
        );
    }
}
#![allow(dead_code)]

use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{alpha1, char, digit1, space0, space1};
use nom::combinator::{self, cut, eof, map, map_opt, peek, success, value, verify};
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
    Abs(String, Box<LamNB>),
    App(Box<LamNB>, Box<LamNB>),
    Add(Box<LamNB>, Box<LamNB>),
    Mul(Box<LamNB>, Box<LamNB>),
    IfElse(Box<LamNB>, Box<LamNB>, Box<LamNB>),
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
        map_opt(terminated(digit1, space0), |s: &'a str| {
            (s.parse::<u32>().ok()).map(Nat)
        }),
    )(input)
}

fn parse_bool<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "bool",
        terminated(
            alt((
                combinator::value(Bool(true), nom::bytes::complete::tag("true")),
                combinator::value(Bool(false), nom::bytes::complete::tag("false")),
            )),
            space0,
        ),
    )(input)
}

fn parse_var<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "var",
        map_opt(terminated(alpha1, space0), |s: &str| {
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
                    map_opt(parse_var, |v| match v {
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
    with_opt_paren(context(
        "prim",
        alt((parse_abs, parse_num, parse_bool, parse_var)),
    ))
    .parse(input)
}

fn parse_app<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "app",
        terminated(chainl1(with_opt_paren(parse_prim), success(app)), space0),
    )
    .parse(input)
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
        map(
            tuple((
                context("if(cond)", preceded(tuple((tag("if"), space1)), parse_add)),
                context(
                    "if(then)",
                    preceded(tuple((tag("then"), space1)), parse_add),
                ),
                context(
                    "if(else)",
                    preceded(tuple((tag("else"), space1)), parse_lamnb),
                ),
            )),
            |(cond, t_expr, f_expr)| if_else(cond, t_expr, f_expr),
        ),
    )(input)
}

// parserをカッコ可能なものに変換する。カッコがあればコンテキストをリセットしてルートからparseし、そうでなければ引数でparseする
fn with_opt_paren<'a, Error>(
    parser: impl Parser<&'a str, LamNB, Error>,
) -> impl Parser<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    alt((
        context(
            "paren",
            delimited(
                tuple((tag("("), space0)),
                parse_lamnb,
                tuple((tag(")"), space0)),
            ),
        ),
        parser,
    ))
}

pub fn parse_lamnb<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "lamnb",
        terminated(
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

pub fn parse_program<'a, Error>(input: &'a str) -> IResult<&'a str, LamNB, Error>
where
    Error: ParseError<&'a str> + ContextError<&'a str>,
{
    context(
        "program",
        delimited(space0, parse_lamnb, tuple((space0, eof))),
    )(input)
}

#[cfg(test)]
mod test {

    use nom::error::VerboseError;
    use nom::Finish as _;

    use super::*;

    fn run<'a>(ipt: &'a str) -> Result<(&'a str, LamNB), VerboseError<&'a str>> {
        parse_program(ipt).finish()
    }

    #[test]
    fn test_parse() {
        assert_eq!(run("1"), Ok(("", nat(1))));
        assert_eq!(run("123"), Ok(("", nat(123))));
        assert_eq!(run("    v  "), Ok(("", var("v".to_string()))));
        assert_eq!(
            run("  1 +   2 + 3 "),
            Ok(("", add(add(nat(1), nat(2)), nat(3))))
        );
        assert_eq!(run("1*2+3"), Ok(("", add(mul(nat(1), nat(2)), nat(3)))));
        assert_eq!(run("1 +2   *3"), Ok(("", add(nat(1), mul(nat(2), nat(3))))));

        assert_eq!(run("\\x.x"), Ok(("", abs("x", var("x")))));
        assert_eq!(run("  \\  x .  x  "), Ok(("", abs("x", var("x")))));

        assert_eq!(run("\\x.x+2"), Ok(("", abs("x", add(var("x"), nat(2))))));

        assert_eq!(
            run("f \\x.f x"),
            Ok(("", app(var("f"), abs("x", app(var("f"), var("x"))))))
        );

        assert_eq!(run("iff"), Ok(("", var("iff"))));
        assert_eq!(
            run("if cond then 1 else 2"),
            Ok(("", if_else(var("cond"), nat(1), nat(2))))
        );
        assert_eq!(
            run("if cond then 1 else \\x.x"),
            Ok(("", if_else(var("cond"), nat(1), abs("x", var("x")))))
        );
        assert_eq!(
            run("\\cond. if cond then 1 else \\x.x"),
            Ok((
                "",
                abs("cond", if_else(var("cond"), nat(1), abs("x", var("x"))))
            ))
        );

        assert_eq!(
            run("if 1 then 2 else if 3 then 4 else 5"),
            Ok(("", if_else(nat(1), nat(2), if_else(nat(3), nat(4), nat(5)))))
        );

        assert_eq!(
            run("if (if 1 then (\\x.x  ) else \\x. f g) then 2 else if 3 then 4 else 5"),
            Ok((
                "",
                if_else(
                    if_else(
                        nat(1),
                        abs("x", var("x")),
                        abs("x", app(var("f"), var("g")))
                    ),
                    nat(2),
                    if_else(nat(3), nat(4), nat(5))
                )
            ))
        );

        assert_eq!(
            run("if (f) v then 2 else if 3 then 4 else 5"),
            Ok((
                "",
                if_else(
                    app(var("f"), var("v")),
                    nat(2),
                    if_else(nat(3), nat(4), nat(5))
                )
            ))
        );

        assert_eq!(
            run("if (if 1 then (\\x.x  ) else \\x. f g) v then 2 else if 3 then 4 else 5"),
            Ok((
                "",
                if_else(
                    app(
                        if_else(
                            nat(1),
                            abs("x", var("x")),
                            abs("x", app(var("f"), var("g")))
                        ),
                        var("v")
                    ),
                    nat(2),
                    if_else(nat(3), nat(4), nat(5))
                )
            ))
        );

        assert_eq!(
            run("f g h"),
            Ok(("", app(app(var("f"), var("g")), var("h"))))
        );

        assert_eq!(
            run("f(g h)"),
            Ok(("", app(var("f"), app(var("g"), var("h")))))
        );

        assert_eq!(
            run("(f g)h"),
            Ok(("", app(app(var("f"), var("g")), var("h"))))
        );
    }
}

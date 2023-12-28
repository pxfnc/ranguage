use nom::error::ParseError;
use nom::Parser;

pub fn chainl1<I, TermParser, BinOpParser, T, Op, Error>(
    mut term: TermParser,
    mut binary_op: BinOpParser,
) -> impl Parser<I, T, Error>
where
    I: Copy,
    Error: ParseError<I>,
    Op: FnOnce(T, T) -> T,
    TermParser: Parser<I, T, Error>,
    BinOpParser: Parser<I, Op, Error>,
{
    move |input| {
        let (mut input, mut lhs) = term.parse(input)?;
        while let Ok((rest, (op, rhs))) = binary_op
            .parse(input)
            .and_then(|(input, op)| term.parse(input).map(|(input, rhs)| (input, (op, rhs))))
        {
            lhs = op(lhs, rhs);
            input = rest;
        }

        Ok((input, lhs))
    }
}

#[cfg(test)]
mod test {

    use super::*;
    use nom::character::complete::{char, digit1};
    use nom::combinator::map;
    #[test]
    fn test_chainl1() {
        let mut parser =
            chainl1::<_, _, _, _, _, ()>(map(digit1, |s: &str| s.to_string()), |ipt| {
                let (ipt, _) = char('+')(ipt)?;
                Ok((ipt, |fst: String, snd: String| format!("({}+{})", fst, snd)))
            });
        assert_eq!(parser.parse("123"), Ok(("", "123".to_string())));
        assert_eq!(
            parser.parse("123+45+67"),
            Ok(("", "((123+45)+67)".to_string()))
        );
    }
}

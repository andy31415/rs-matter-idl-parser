use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_until},
    character::complete::one_of,
    combinator::{map, map_res, recognize, value},
    multi::many1,
    sequence::{pair, preceded, tuple},
    IResult,
};
use nom_locate::LocatedSpan;

// easier to type and not move str around
type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum ApiMaturity {
    STABLE,
    PROVISIONAL,
    INTERNAL,
    DEPRECATED,
}

/// A parser that CANNOT fail
///
/// Note that it will consume no input if no maturity is specified
/// in which case it returns 'STABLE'
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::{parse_api_maturity, ApiMaturity};
///
/// assert_eq!(
///    parse_api_maturity("123".into()),
///    Ok(("123".into(), ApiMaturity::STABLE))
/// );
///
/// let result = parse_api_maturity("provisional 123".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " 123");
/// assert_eq!(result.1, ApiMaturity::PROVISIONAL);
/// ```
pub fn parse_api_maturity(span: Span) -> IResult<Span, ApiMaturity> {
    let specified: IResult<Span, ApiMaturity> = alt((
        map(tag("stable"), |_| ApiMaturity::STABLE),
        map(tag("provisional"), |_| ApiMaturity::PROVISIONAL),
        map(tag("internal"), |_| ApiMaturity::INTERNAL),
        map(tag("deprecated"), |_| ApiMaturity::DEPRECATED),
    ))(span);

    // This actually cannot fail
    if specified.is_err() {
        // Do not consume anything, return stable if not specified
        return Ok((span, ApiMaturity::STABLE));
    }

    specified
}

/// Parses a hex-formated integer
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::parse_hex_integer;
///
/// let result = parse_hex_integer("0x12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 0x12);
///
/// let result = parse_hex_integer("0X12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "test");
/// assert_eq!(result.1, 0x12abc);
/// ```
pub fn parse_hex_integer(span: Span) -> IResult<Span, u32> {
    preceded(
        alt((tag("0x"), tag("0X"))),
        map_res(
            recognize(many1(one_of("0123456789abcdefABCDEF"))),
            |r: Span| u32::from_str_radix(&r, 16),
        ),
    )(span)
}

/// Parses a decimal-formated integer
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::parse_decimal_integer;
///
/// let result = parse_decimal_integer("12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 12);
///
/// let result = parse_decimal_integer("12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abctest");
/// assert_eq!(result.1, 12);
/// ```
pub fn parse_decimal_integer(span: Span) -> IResult<Span, u32> {
    map_res(recognize(many1(one_of("0123456789"))), |r: Span| {
        r.parse::<u32>()
    })(span)
}

/// Parses a positive integer (hex or decimal)
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::parse_positive_integer;
///
/// let result = parse_positive_integer("12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 12);
///
/// let result = parse_positive_integer("12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abctest");
/// assert_eq!(result.1, 12);
///
/// let result = parse_positive_integer("0x12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "test");
/// assert_eq!(result.1, 0x12abc);
/// ```
pub fn parse_positive_integer(span: Span) -> IResult<Span, u32> {
    // NOTE: orer is important so that
    // 0x123 is a hex not 0 followed by "x123"
    alt((parse_hex_integer, parse_decimal_integer))(span)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DocComment<'a>(&'a str);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Whitespace<'a> {
    DocComment(&'a str), // /** ... */
    CppComment(&'a str), // /* ... */ (and NOT a doc comment)
    CComment(&'a str),   // // ....
    Whitespace,          // general newline/space/tab
}

/// Parses whitespace (space/tab/newline and comments).
///
/// returns the content of the comment
pub fn parse_whitespace(span: Span) -> IResult<Span, Whitespace<'_>> {
    // C-style comment, output thrown away
    let result = map::<Span, _, _, _, _, _>(pair(tag("//"), is_not("\n\r")), |(_, comment)| {
        Whitespace::CComment(comment.fragment())
    })(span);
    if result.is_ok() {
        return result;
    }

    // C++-style comment, output thrown away
    let result = map(
        tuple((tag::<&str, Span, _>("/*"), take_until("*/"), tag("*/"))),
        |(_, comment, _)| {
            if comment.starts_with("*") {
                Whitespace::DocComment(&comment.fragment()[1..])
            } else {
                Whitespace::CppComment(comment.fragment())
            }
        },
    )(span);
    if result.is_ok() {
        return result;
    }

    // Finally just consume the whitespace
    value(Whitespace::Whitespace, many1(one_of(" \t\r\n")))(span)
}

/// Parses at least one whitespace
/// If the last comment whitespace is a doccomment, then
/// It returns that doc comment.
///
pub fn whitespace1(span: Span) -> IResult<Span, Option<DocComment>> {
    let mut doc: Option<DocComment> = None;

    let mut parsed = parse_whitespace(span)?;

    if let Whitespace::DocComment(comment) = parsed.1 {
        doc = Some(DocComment(comment))
    }

    // now consume all other results if any
    loop {
        match parse_whitespace(parsed.0) {
            Ok((span, whitespace)) => {
                parsed = (span, whitespace);
                match whitespace {
                   Whitespace::DocComment(comment) => doc = Some(DocComment(comment)),
                   Whitespace::CComment(_) => doc = None,
                   Whitespace::CppComment(_) => doc = None,
                   Whitespace::Whitespace => {},
                }
            }
            Err(_) => return Ok((parsed.0, doc)),
        }
    }
}

// TODO:
// constant_entry: [maturity] id "=" positive_integer ";"

#[cfg(test)]
mod tests {
    use super::*;

    fn remove_loc<O>(src: IResult<Span, O>) -> IResult<Span, O> {
        src.map(|(span, o)| ((*span.fragment()).into(), o))
    }

    #[test]
    fn test_parse_maturity() {
        assert_eq!(
            parse_api_maturity("123".into()),
            Ok(("123".into(), ApiMaturity::STABLE))
        );
        assert_eq!(
            remove_loc(parse_api_maturity("stable abc".into())),
            Ok((" abc".into(), ApiMaturity::STABLE))
        );
        assert_eq!(
            remove_loc(parse_api_maturity("provisional abc".into())),
            Ok((" abc".into(), ApiMaturity::PROVISIONAL))
        );
        assert_eq!(
            remove_loc(parse_api_maturity("internal xyz".into())),
            Ok((" xyz".into(), ApiMaturity::INTERNAL))
        );
        assert_eq!(
            remove_loc(parse_api_maturity("deprecated foobar".into())),
            Ok((" foobar".into(), ApiMaturity::DEPRECATED))
        );
    }

    #[test]
    fn test_parse_hex_integer() {
        assert!(parse_hex_integer("".into()).is_err());
        assert!(parse_hex_integer("123".into()).is_err());
        assert!(parse_hex_integer("0xzzz".into()).is_err());
        assert!(parse_hex_integer("0x".into()).is_err());

        assert_eq!(
            remove_loc(parse_hex_integer("0x12 abc".into())),
            Ok((" abc".into(), 0x12))
        );
        assert_eq!(
            remove_loc(parse_hex_integer("0XABC XYZ".into())),
            Ok((" XYZ".into(), 0xABC))
        );
    }

    #[test]
    fn test_parse_decimal() {
        assert!(parse_decimal_integer("a".into()).is_err());
        assert!(parse_decimal_integer("".into()).is_err());

        assert_eq!(
            remove_loc(parse_decimal_integer("123".into())),
            Ok(("".into(), 123))
        );
        assert_eq!(
            remove_loc(parse_decimal_integer("1 2 3".into())),
            Ok((" 2 3".into(), 1))
        );
        assert_eq!(
            remove_loc(parse_decimal_integer("0x123".into())),
            Ok(("x123".into(), 0))
        );
    }

    #[test]
    fn test_parse_positive_integer() {
        assert!(parse_positive_integer("a".into()).is_err());
        assert!(parse_positive_integer("".into()).is_err());

        assert_eq!(
            remove_loc(parse_positive_integer("123".into())),
            Ok(("".into(), 123))
        );
        assert_eq!(
            remove_loc(parse_positive_integer("1 2 3".into())),
            Ok((" 2 3".into(), 1))
        );
        assert_eq!(
            remove_loc(parse_positive_integer("0x123".into())),
            Ok(("".into(), 0x123))
        );
        assert_eq!(
            remove_loc(parse_positive_integer("12ab".into())),
            Ok(("ab".into(), 12))
        );
        assert_eq!(
            remove_loc(parse_positive_integer("0x12abcxyz".into())),
            Ok(("xyz".into(), 0x12abc))
        );
    }

    #[test]
    fn test_parse_whitespace() {
        assert!(parse_whitespace("a".into()).is_err());
        assert!(parse_whitespace("".into()).is_err());

        assert_eq!(
            remove_loc(parse_whitespace("   abc".into())),
            Ok(("abc".into(), Whitespace::Whitespace))
        );
        assert_eq!(
            remove_loc(parse_whitespace("/* cpp comment */rest of text".into())),
            Ok((
                "rest of text".into(),
                Whitespace::CppComment(" cpp comment ")
            ))
        );
        assert_eq!(
            remove_loc(parse_whitespace("/** Doc comment */rest of text".into())),
            Ok((
                "rest of text".into(),
                Whitespace::DocComment(" Doc comment ")
            ))
        );

        // only one (first) whitespace is removed
        assert_eq!(
            remove_loc(parse_whitespace("//test   \nxyz".into())),
            Ok(("\nxyz".into(), Whitespace::CComment("test   ")))
        );
        assert_eq!(
            remove_loc(parse_whitespace("  \n//test   \nxyz".into())),
            Ok(("//test   \nxyz".into(), Whitespace::Whitespace))
        );
    }
}

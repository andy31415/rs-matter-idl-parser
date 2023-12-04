use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::one_of,
    combinator::{map, map_res, recognize},
    multi::many1,
    sequence::preceded,
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

// positive_integer: POSITIVE_INTEGER | HEX_INTEGER
// POSITIVE_INTEGER: /\d+/
// HEX_INTEGER: /0x[A-Fa-f0-9]+/

pub fn parse_hex_integer(span: Span) -> IResult<Span, u32> {
    preceded(
        alt((tag("0x"), tag("0X"))),
        map_res(
            recognize(many1(one_of("0123456789abcdefABCDEF"))),
            |r: Span| u32::from_str_radix(&r, 16),
        ),
    )(span)
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
}

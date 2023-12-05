use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, tag_no_case, take_until, take_while, take_while1},
    character::complete::{hex_digit1, one_of},
    combinator::{map, map_res, opt, recognize},
    error::{Error as NomError, ErrorKind},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded, tuple},
    IResult, Parser,
};
use nom_locate::LocatedSpan;

// easier to type and not move str around
type Span<'a> = LocatedSpan<&'a str>;

#[derive(Debug, PartialEq, Copy, Clone, Hash, PartialOrd, Eq, Ord)]
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
        map(tag_no_case("stable"), |_| ApiMaturity::STABLE),
        map(tag_no_case("provisional"), |_| ApiMaturity::PROVISIONAL),
        map(tag_no_case("internal"), |_| ApiMaturity::INTERNAL),
        map(tag_no_case("deprecated"), |_| ApiMaturity::DEPRECATED),
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
        tag_no_case("0x"),
        map_res(recognize(hex_digit1), |r: Span| u32::from_str_radix(&r, 16)),
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

/// Represents a comment (i.e. something between `/** ... */`)
///
/// Typically placed before some element (e.g. cluster or command) to serve
/// as documentation for it.
///
/// Parsing whitespace yields doc-comments if the last comment in a whitespace
/// sequence is a doc comment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DocComment<'a>(pub &'a str);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Whitespace<'a> {
    DocComment(&'a str), // /** ... */
    CppComment(&'a str), // /* ... */ (and NOT a doc comment)
    CComment(&'a str),   // // ....
    Whitespace(&'a str), // general newline/space/tab
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
            if comment.starts_with('*') {
                Whitespace::DocComment(&comment.fragment()[1..])
            } else {
                Whitespace::CppComment(comment.fragment())
            }
        },
    )(span);
    if result.is_ok() {
        return result;
    }

    let is_space = |c: char| -> bool { c == ' ' || c == '\r' || c == '\n' || c == '\t' };

    // Finally just consume the whitespace
    map::<Span, _, _, _, _, _>(take_while1(is_space), |comment| {
        Whitespace::Whitespace(&comment)
    })(span)
}

/// Parses 0 or more whitespaces.
/// It can NEVER fail.
///
/// If the last comment whitespace is a doc-comment, returns
/// that doc-comment.
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::{whitespace0, DocComment};
///
/// let result = whitespace0(" /*comment*/\n12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "12 abc");
/// assert_eq!(result.1, None);
///
/// let result = whitespace0(" /**doc comment*/\n abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abc");
/// assert_eq!(result.1, Some(DocComment("doc comment")));
///
/// let result = whitespace0("no whitespace".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "no whitespace");
/// assert_eq!(result.1, None);
/// ```
pub fn whitespace0(span: Span) -> IResult<Span, Option<DocComment>> {
    let mut doc: Option<DocComment> = None;

    let mut parsed = match parse_whitespace(span) {
        Err(_) => return Ok((span, None)),
        Ok(value) => value,
    };

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
                    Whitespace::Whitespace(_) => {}
                }
            }
            Err(_) => return Ok((parsed.0, doc)),
        }
    }
}

/// Parses at least one whitespace
/// If the last comment whitespace is a doccomment, then
/// It returns that doc comment.
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::{whitespace1, DocComment};
///
/// let result = whitespace1(" /*comment*/\n12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "12 abc");
/// assert_eq!(result.1, None);
///
/// let result = whitespace1(" /**doc comment*/\n abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abc");
/// assert_eq!(result.1, Some(DocComment("doc comment")));
/// ```
pub fn whitespace1(span: Span) -> IResult<Span, Option<DocComment>> {
    let parsed = whitespace0(span)?;

    if span == parsed.0 {
        // TODO: how do I make a proper error without
        //       using internal errors?
        return Err(nom::Err::Error(NomError {
            input: span,
            code: ErrorKind::Space,
        }));
    }

    Ok(parsed)
}

/// Parses a name id, of the form /[a-zA-Z_][a-zA-Z0-9_]*/
///
pub fn parse_id(span: Span) -> IResult<Span, &str> {
    let valid_first = |c: char| c.is_ascii_alphabetic() || c == '_';
    let valid_second = |c: char| c.is_ascii_alphanumeric() || c == '_';
    map(
        recognize(tuple((take_while1(valid_first), take_while(valid_second)))),
        |data: Span| *data.fragment(),
    )(span)
}

/// A named numeric value.
///
/// A value that has a name (e.g. enumeration or bitmap constant).
/// May also have an associated maturity that defaults to STABLE
/// while parsing.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstantEntry<'a> {
    pub maturity: ApiMaturity,
    pub id: &'a str,
    pub code: u32,
}

impl<'a> ConstantEntry<'a> {
    /// Parses a IDL representation of a constant entry.
    ///
    /// Consumes any whitespace BEFORE the entry.
    ///
    /// Examples:
    ///
    /// ```
    /// use rs_matter_idl_parser::{ConstantEntry, ApiMaturity};
    ///
    /// let parsed = ConstantEntry::parse("provisional kConstant = 0x123 ;".into()).expect("valid");
    /// assert_eq!(parsed.0.fragment().to_string(), "");
    /// assert_eq!(
    ///         parsed.1,
    ///         ConstantEntry {
    ///             id: "kConstant",
    ///             code: 0x123,
    ///             maturity: ApiMaturity::PROVISIONAL
    ///         }
    /// );
    /// ```
    pub fn parse(span: Span) -> IResult<Span, ConstantEntry<'_>> {
        tuple((
            whitespace0,
            parse_api_maturity,
            whitespace0,
            parse_id,
            whitespace0,
            tag("="),
            whitespace0,
            parse_positive_integer,
            whitespace0,
            tag(";"),
        ))
        .map(|(_, maturity, _, id, _, _, _, code, _, _)| ConstantEntry { maturity, id, code })
        .parse(span)
    }
}

/// Parses a list of constant entries, delimeted by "{" "}".
///
/// Consumes the '{' '}' as well as any internal whitespace in them
fn constant_entries_list(span: Span) -> IResult<Span, Vec<ConstantEntry<'_>>> {
    delimited(
        tag("{"),
        tuple((
            many0(tuple((whitespace0, ConstantEntry::parse)).map(|(_, v)| v)),
            whitespace0,
        )),
        tag("}"),
    )
    .map(|(v, _)| v)
    .parse(span)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Enum<'a> {
    pub doc_comment: Option<&'a str>,
    pub maturity: ApiMaturity,
    pub id: &'a str,
    pub base_type: &'a str,
    pub entries: Vec<ConstantEntry<'a>>,
}

impl<'a> Enum<'a> {
    pub fn parse(span: Span) -> IResult<Span, Enum<'_>> {
        let (span, comment) = whitespace0(span)?;
        let doc_comment = comment.map(|DocComment(comment)| comment);
        let (span, maturity) = tuple((parse_api_maturity, whitespace0))
            .map(|(m, _)| m)
            .parse(span)?;

        tuple((
            tag_no_case("enum"),
            whitespace1,
            parse_id,
            whitespace0,
            tag(":"),
            whitespace0,
            parse_id,
            whitespace0,
            constant_entries_list,
        ))
        .map(|(_, _, id, _, _, _, base_type, _, entries)| Enum {
            doc_comment,
            maturity,
            id,
            base_type,
            entries,
        })
        .parse(span)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bitmap<'a> {
    pub doc_comment: Option<&'a str>,
    pub maturity: ApiMaturity,
    pub id: &'a str,
    pub base_type: &'a str,
    pub entries: Vec<ConstantEntry<'a>>,
}

impl<'a> Bitmap<'a> {
    pub fn parse(span: Span) -> IResult<Span, Bitmap<'_>> {
        let (span, comment) = whitespace0(span)?;
        let doc_comment = comment.map(|DocComment(comment)| comment);
        let (span, maturity) = tuple((parse_api_maturity, whitespace0))
            .map(|(m, _)| m)
            .parse(span)?;

        tuple((
            tag_no_case("bitmap"),
            whitespace1,
            parse_id,
            whitespace0,
            tag(":"),
            whitespace0,
            parse_id,
            whitespace0,
            constant_entries_list,
        ))
        .map(|(_, _, id, _, _, _, base_type, _, entries)| Bitmap {
            doc_comment,
            maturity,
            id,
            base_type,
            entries,
        })
        .parse(span)
    }
}

/// A generic type such as integers, strings, enums etc.
///
/// Supports information if this is repeated/list as well
/// as a maximum length (if applicable).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DataType<'a> {
    name: &'a str,
    is_list: bool,
    max_length: Option<u32>,
}

impl<'a> DataType<'a> {
    pub fn scalar(name: &'_ str) -> DataType<'_> {
        DataType {
            name,
            is_list: false,
            max_length: None,
        }
    }

    pub fn list_of(name: &'_ str) -> DataType<'_> {
        DataType {
            name,
            is_list: true,
            max_length: None,
        }
    }

    pub fn scalar_of_size(name: &'_ str, max_length: u32) -> DataType<'_> {
        DataType {
            name,
            is_list: false,
            max_length: Some(max_length),
        }
    }
}

/// Represents a generic field.
///
/// Fields have a type, name(id) and numeric code.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Field<'a> {
    pub data_type: DataType<'a>,
    pub id: &'a str,
    pub code: u32,
}

impl<'a> Field<'a> {
    pub fn parse(span: Span) -> IResult<Span, Field<'_>> {
        tuple((
            whitespace0,
            parse_id,
            opt(tuple((
                whitespace0,
                tag("<"),
                whitespace0,
                parse_positive_integer,
                whitespace0,
                tag(">"),
            ))
            .map(|(_, _, _, pos, _, _)| pos)),
            whitespace1,
            parse_id,
            whitespace0,
            opt(tuple((tag("["), whitespace0, tag("]"), whitespace0))),
            tag("="),
            whitespace0,
            parse_positive_integer,
        ))
        .map(
            |(_, type_name, max_length, _, id, _, list_marker, _, _, code)| Field {
                data_type: DataType {
                    name: type_name,
                    is_list: list_marker.is_some(),
                    max_length,
                },
                id,
                code,
            },
        )
        .parse(span)
    }
}

/// Represents a field entry within a struct.
///
/// Specifically this adds structure specific information
/// such as API maturity, optional/nullable/fabric_sensitive
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StructField<'a> {
    pub field: Field<'a>,
    pub maturity: ApiMaturity,
    pub optional: bool,
    pub nullable: bool,
    pub fabric_sensitive: bool,
}

impl<'a> StructField<'a> {
    pub fn parse(span: Span) -> IResult<Span, StructField<'_>> {
        todo!();
    }
}

// TODO: structs
//    - needs fields (generic: structs and events have these)
//    - within fields making struc fields
//
// struct: struct_qualities "struct"i id "{" (struct_field ";")* "}"
// struct_qualities: struct_quality*
// struct_quality: "fabric_scoped"i -> struct_fabric_scoped
//
// struct_field: [maturity] member_attribute* field
//
// member_attribute: "optional"i -> optional
//                   "nullable"i -> nullable
//                   "fabric_sensitive"i -> fabric_sensitive
//
// field: data_type id list_marker? "=" positive_integer
// list_marker: "[" "]"
// data_type: type ("<" positive_integer ">")?

#[cfg(test)]
mod tests {
    use super::*;

    fn remove_loc<O>(src: IResult<Span, O>) -> IResult<Span, O> {
        src.map(|(span, o)| ((*span.fragment()).into(), o))
    }

    fn assert_parse_ok<R: PartialEq + std::fmt::Debug>(parsed: IResult<Span, R>, expected: R) {
        let actual = parsed.expect("Parse should have succeeded").1;
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_parse_field() {
        assert_parse_ok(
            Field::parse("bool test = 1".into()),
            Field {
                data_type: DataType::scalar("bool"),
                id: "test",
                code: 1,
            },
        );
        assert_parse_ok(
            Field::parse("int32u test[] = 0x12".into()),
            Field {
                data_type: DataType::list_of("int32u"),
                id: "test",
                code: 0x12,
            },
        );
        assert_parse_ok(
            Field::parse("octet_string<123> other=10".into()),
            Field {
                data_type: DataType::scalar_of_size("octet_string", 123),
                id: "other",
                code: 10,
            },
        );
    }

    #[test]
    fn test_parse_enum() {
        assert_parse_ok(
            Enum::parse(
                "
  enum EffectIdentifierEnum : enum8 {
    kBlink = 0;
    kBreathe = 1;
    kOkay = 2;
    kChannelChange = 11;
    kFinishEffect = 254;
    kStopEffect = 255;
  }"
                .into(),
            ),
            Enum {
                doc_comment: None,
                maturity: ApiMaturity::STABLE,
                id: "EffectIdentifierEnum",
                base_type: "enum8",
                entries: vec![
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kBlink",
                        code: 0,
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kBreathe",
                        code: 1,
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kOkay",
                        code: 2,
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kChannelChange",
                        code: 11,
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kFinishEffect",
                        code: 254,
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kStopEffect",
                        code: 255,
                    },
                ],
            },
        );
    }

    #[test]
    fn test_parse_bitmap() {
        assert_eq!(
            Bitmap::parse(
                "
  /** Test feature bitmap */
  bitmap Feature : bitmap32 {
    kSceneNames = 0x1;
    kExplicit = 0x2;
    kTableSize = 0x4;
    provisional kFabricScenes = 0x8;
  }"
                .into()
            )
            .expect("valid value")
            .1,
            Bitmap {
                doc_comment: Some(" Test feature bitmap "),
                maturity: ApiMaturity::STABLE,
                id: "Feature",
                base_type: "bitmap32",
                entries: vec![
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kSceneNames",
                        code: 0x01
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kExplicit",
                        code: 0x02
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kTableSize",
                        code: 0x04
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::PROVISIONAL,
                        id: "kFabricScenes",
                        code: 0x08
                    },
                ]
            }
        );
    }

    #[test]
    fn test_parse_constant_entry_list() {
        assert_eq!(
            remove_loc(constant_entries_list("{}".into())),
            Ok(("".into(), vec![]))
        );
        assert_eq!(
            remove_loc(constant_entries_list(
                "{ a = 1; provisional b = 2; }".into()
            )),
            Ok((
                "".into(),
                vec![
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "a",
                        code: 1
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::PROVISIONAL,
                        id: "b",
                        code: 2
                    },
                ]
            ))
        );
        assert_eq!(
            remove_loc(constant_entries_list(
                "{
                // Comment
                kConstantOne = 123; 
                internal kAnother = 0x23abc /* this tests hex */; 
            }suffix"
                    .into()
            )),
            Ok((
                "suffix".into(),
                vec![
                    ConstantEntry {
                        maturity: ApiMaturity::STABLE,
                        id: "kConstantOne",
                        code: 123
                    },
                    ConstantEntry {
                        maturity: ApiMaturity::INTERNAL,
                        id: "kAnother",
                        code: 0x23abc
                    },
                ]
            ))
        );
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

        assert_eq!(
            remove_loc(parse_api_maturity("DepreCAteD CaseTest".into())),
            Ok((" CaseTest".into(), ApiMaturity::DEPRECATED))
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
            Ok(("abc".into(), Whitespace::Whitespace("   ")))
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
            Ok(("//test   \nxyz".into(), Whitespace::Whitespace("  \n")))
        );
    }

    #[test]
    fn test_parse_whitespace1() {
        assert!(whitespace1("a".into()).is_err());
        assert!(whitespace1("".into()).is_err());

        assert_eq!(
            remove_loc(whitespace1("//test\n123".into())),
            Ok(("123".into(), None))
        );
        assert_eq!(
            remove_loc(whitespace1("//test\n/*cpp */  \t  \t\r\n123".into())),
            Ok(("123".into(), None))
        );

        // doc comments are extracted
        assert_eq!(
            remove_loc(whitespace1("//test\n/** Comment! */123".into())),
            Ok(("123".into(), Some(DocComment(" Comment! "))))
        );
        assert_eq!(
            remove_loc(whitespace1("//test\n/** Comment! */\n\n  \n\n123".into())),
            Ok(("123".into(), Some(DocComment(" Comment! "))))
        );
        assert_eq!(
            remove_loc(whitespace1("/** Comment! *///separated\n123".into())),
            Ok(("123".into(), None))
        );
        assert_eq!(
            remove_loc(whitespace1("/** Comment! *//*separated*/123".into())),
            Ok(("123".into(), None))
        );
    }

    #[test]
    fn test_parse_whitespace0() {
        assert_eq!(remove_loc(whitespace0("a".into())), Ok(("a".into(), None)));
        assert_eq!(remove_loc(whitespace0("".into())), Ok(("".into(), None)));
        assert_eq!(
            remove_loc(whitespace0("//test\n/** Comment! */123".into())),
            Ok(("123".into(), Some(DocComment(" Comment! "))))
        );
        assert_eq!(
            remove_loc(whitespace0("/** Comment! *//*separated*/123".into())),
            Ok(("123".into(), None))
        );
    }

    #[test]
    fn test_parse_id() {
        assert!(parse_id("  xyz".into()).is_err());
        assert!(parse_id("/".into()).is_err());
        assert!(parse_id("#test".into()).is_err());
        assert!(parse_id("123abc".into()).is_err());

        assert_eq!(
            remove_loc(parse_id("abc123 other".into())),
            Ok((" other".into(), "abc123"))
        );
        assert_eq!(
            remove_loc(parse_id("this_is_a_test and more data".into())),
            Ok((" and more data".into(), "this_is_a_test"))
        );
        assert_eq!(
            remove_loc(parse_id("_Test 123".into())),
            Ok((" 123".into(), "_Test"))
        );
    }

    #[test]
    fn test_parse_constant_entry() {
        assert!(ConstantEntry::parse("abc".into()).is_err());
        assert!(ConstantEntry::parse("a = 1".into()).is_err());
        assert!(ConstantEntry::parse("a = ;".into()).is_err());
        assert!(ConstantEntry::parse("provisional a = ;".into()).is_err());

        assert_eq!(
            remove_loc(ConstantEntry::parse("a=0;".into())),
            Ok((
                "".into(),
                ConstantEntry {
                    id: "a",
                    code: 0,
                    maturity: ApiMaturity::STABLE
                }
            ))
        );

        assert_eq!(
            remove_loc(ConstantEntry::parse("   provisional xyz = 0x123 ;".into())),
            Ok((
                "".into(),
                ConstantEntry {
                    id: "xyz",
                    code: 0x123,
                    maturity: ApiMaturity::PROVISIONAL
                }
            ))
        );

        assert_eq!(
            remove_loc(ConstantEntry::parse("InterNAL kTest = 0xabc ;".into())),
            Ok((
                "".into(),
                ConstantEntry {
                    id: "kTest",
                    code: 0xABC,
                    maturity: ApiMaturity::INTERNAL
                }
            ))
        );
        assert_eq!(
            remove_loc(ConstantEntry::parse(
                "
                internal
                kTest\t
                     =
                      0xabc
                  
                       ;"
                .into()
            )),
            Ok((
                "".into(),
                ConstantEntry {
                    id: "kTest",
                    code: 0xABC,
                    maturity: ApiMaturity::INTERNAL
                }
            ))
        );
        assert_eq!(
            remove_loc(ConstantEntry::parse(
                "
            /*comment*/ internal
            //test
            kTest //more comments
                 = /*test*/
                   // and more
                  0xabc //test ;;; these are in comments ;;;
                  ;"
                .into()
            )),
            Ok((
                "".into(),
                ConstantEntry {
                    id: "kTest",
                    code: 0xABC,
                    maturity: ApiMaturity::INTERNAL
                }
            ))
        );
    }
}

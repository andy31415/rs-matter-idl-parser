use std::collections::HashSet;

use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, tag_no_case, take_until, take_while, take_while1},
    character::complete::{hex_digit1, one_of},
    combinator::{map, map_res, opt, recognize, value},
    error::{Error as NomError, ErrorKind},
    multi::{many0, many1, separated_list0},
    sequence::{delimited, pair, preceded, tuple},
    IResult, Parser,
};
use nom_locate::LocatedSpan;

// easier to type and not move str around
type Span<'a> = LocatedSpan<&'a str>;

/// How mature/usable a member of an API is
///
/// Most things should be stable, however while spec is developed
/// we expect PROVISIONAL to be set.
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
/// use rs_matter_idl_parser::{api_maturity, ApiMaturity};
///
/// assert_eq!(
///    api_maturity("123".into()),
///    Ok(("123".into(), ApiMaturity::STABLE))
/// );
///
/// let result = api_maturity("provisional 123".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " 123");
/// assert_eq!(result.1, ApiMaturity::PROVISIONAL);
/// ```
pub fn api_maturity(span: Span) -> IResult<Span, ApiMaturity> {
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
/// use rs_matter_idl_parser::hex_integer;
///
/// let result = hex_integer("0x12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 0x12);
///
/// let result = hex_integer("0X12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "test");
/// assert_eq!(result.1, 0x12abc);
/// ```
pub fn hex_integer(span: Span) -> IResult<Span, u32> {
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
/// use rs_matter_idl_parser::decimal_integer;
///
/// let result = decimal_integer("12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 12);
///
/// let result = decimal_integer("12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abctest");
/// assert_eq!(result.1, 12);
/// ```
pub fn decimal_integer(span: Span) -> IResult<Span, u32> {
    map_res(recognize(many1(one_of("0123456789"))), |r: Span| {
        r.parse::<u32>()
    })(span)
}

/// Parses a positive integer (hex or decimal)
///
/// Examples:
///
/// ```
/// use rs_matter_idl_parser::positive_integer;
///
/// let result = positive_integer("12 abc".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), " abc");
/// assert_eq!(result.1, 12);
///
/// let result = positive_integer("12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "abctest");
/// assert_eq!(result.1, 12);
///
/// let result = positive_integer("0x12abctest".into()).expect("Valid");
/// assert_eq!(result.0.fragment().to_string(), "test");
/// assert_eq!(result.1, 0x12abc);
/// ```
pub fn positive_integer(span: Span) -> IResult<Span, u32> {
    // NOTE: orer is important so that
    // 0x123 is a hex not 0 followed by "x123"
    alt((hex_integer, decimal_integer))(span)
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

/// Information returned while parsing whitespace.
///
/// Contains the underlying content of the whitespace, which is
/// especially useful for documentation comments.
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
pub fn whitespace_group(span: Span) -> IResult<Span, Whitespace<'_>> {
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

    let mut parsed = match whitespace_group(span) {
        Err(_) => return Ok((span, None)),
        Ok(value) => value,
    };

    if let Whitespace::DocComment(comment) = parsed.1 {
        doc = Some(DocComment(comment))
    }

    // now consume all other results if any
    loop {
        match whitespace_group(parsed.0) {
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
            api_maturity,
            whitespace0,
            parse_id,
            whitespace0,
            tag("="),
            whitespace0,
            positive_integer,
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

/// A set of constant entries that correspont to an enumeration.
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
        let (span, maturity) = tuple((api_maturity, whitespace0))
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

/// A set of constant entries that correspont to a bitmap.
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
        let (span, maturity) = tuple((api_maturity, whitespace0))
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

impl Field<'_> {
    pub fn parse(span: Span) -> IResult<Span, Field<'_>> {
        tuple((
            whitespace0,
            parse_id,
            opt(tuple((
                whitespace0,
                tag("<"),
                whitespace0,
                positive_integer,
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
            positive_integer,
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
    pub is_optional: bool,
    pub is_nullable: bool,
    pub is_fabric_sensitive: bool,
}

impl StructField<'_> {
    pub fn parse(span: Span) -> IResult<Span, StructField<'_>> {
        let (span, maturity) = tuple((whitespace0, api_maturity, whitespace0))
            .map(|(_, m, _)| m)
            .parse(span)?;

        let (span, attributes): (_, HashSet<&'_ str>) = separated_list0(
            whitespace1,
            alt((
                tag_no_case("optional"),
                tag_no_case("nullable"),
                tag_no_case("fabric_sensitive"),
            )),
        )
        .map(|attrs| HashSet::from_iter(attrs.iter().map(|s| *s.fragment())))
        .parse(span)?;

        let is_optional = attributes.contains("optional");
        let is_nullable = attributes.contains("nullable");
        let is_fabric_sensitive = attributes.contains("fabric_sensitive");

        let (span, field) = Field::parse(span)?;

        Ok((
            span,
            StructField {
                field,
                maturity,
                is_optional,
                is_nullable,
                is_fabric_sensitive,
            },
        ))
    }
}

/// Defines the type of a structure.
///
/// Response structures contain the underlying code used to send
/// that structure as a reply.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StructType {
    Regular,
    Request,
    Response(u32), // response with a code
}

/// A structure defined in IDL.
///
/// Structures may be regular (as data types), request (used in command inputs)
/// or responses (used as command outputs, have an id)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Struct<'a> {
    pub struct_type: StructType,
    pub id: &'a str,
    pub fields: Vec<StructField<'a>>,
    pub is_fabric_scoped: bool,
}

impl Struct<'_> {
    pub fn parse(span: Span) -> IResult<Span, Struct<'_>> {
        let (span, _) = whitespace0.parse(span)?;

        let (span, struct_type) =
            opt(alt((tag_no_case("request"), tag_no_case("response"))))(span)?;
        let struct_type = struct_type.map(|f| *f.fragment());

        let (span, _) = whitespace0.parse(span)?;

        let (span, attributes): (_, HashSet<&'_ str>) =
            separated_list0(whitespace1, tag_no_case("fabric_scoped"))
                .map(|attrs| HashSet::from_iter(attrs.iter().map(|s| *s.fragment())))
                .parse(span)?;

        let is_fabric_scoped = attributes.contains("fabric_scoped");

        let (span, id) = tuple((tag_no_case("struct"), whitespace1, parse_id, whitespace0))
            .map(|(_, _, id, _)| id)
            .parse(span)?;

        let (span, struct_type) = match struct_type {
            Some("request") => (span, StructType::Request),
            Some("response") => tuple((tag("="), whitespace0, positive_integer, whitespace0))
                .map(|(_, _, id, _)| StructType::Response(id))
                .parse(span)?,
            _ => (span, StructType::Regular),
        };

        let (span, fields) = delimited(
            tag("{"),
            many0(
                tuple((
                    whitespace0,
                    StructField::parse,
                    whitespace0,
                    tag(";"),
                    whitespace0,
                ))
                .map(|(_, f, _, _, _)| f),
            ),
            tag("}"),
        )
        .parse(span)?;

        Ok((
            span,
            Struct {
                struct_type,
                id,
                fields,
                is_fabric_scoped,
            },
        ))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AccessPrivilege {
    View,
    Operate,
    Manage,
    Administer,
}

pub fn access_privilege(span: Span) -> IResult<Span, AccessPrivilege> {
    alt((
        value(AccessPrivilege::View, tag_no_case("view")),
        value(AccessPrivilege::Operate, tag_no_case("operate")),
        value(AccessPrivilege::Manage, tag_no_case("manage")),
        value(AccessPrivilege::Administer, tag_no_case("administer")),
    ))(span)
}

// TODO: events
// event: event_qualities event_priority event_with_access "=" positive_integer "{" (struct_field ";")* "}"
// event_qualities: event_quality*
// event_quality: "fabric_sensitive" -> event_fabric_sensitive
// ?event_priority: "critical"i -> critical_priority
//               | "info"i     -> info_priority
//               | "debug"i    -> debug_priority
// event_with_access: "event" event_access? id
// event_access: "access" "(" ("read" ":" access_privilege)? ")"
// ?access_privilege: "view"i       -> view_privilege
//                  | "operate"i    -> operate_privilege
//                  | "manage"i     -> manage_privilege
//                  | "administer"i -> administer_privilege

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
    fn test_parse_access_privilege() {
        assert!(access_privilege("xyz".into()).is_err());
        assert!(access_privilege("FooBar".into()).is_err());
        assert!(access_privilege("MaybeView".into()).is_err());

        // does NOT consume whitespace
        assert!(access_privilege("   view".into()).is_err());
        assert!(access_privilege("   manage   ".into()).is_err());

        assert_parse_ok(access_privilege("view".into()), AccessPrivilege::View);
        assert_parse_ok(access_privilege("operate".into()), AccessPrivilege::Operate);
        assert_parse_ok(access_privilege("ManaGe".into()), AccessPrivilege::Manage);
        assert_parse_ok(
            access_privilege("adminisTER".into()),
            AccessPrivilege::Administer,
        );
    }

    #[test]
    fn test_parse_struct() {
        assert_parse_ok(
            Struct::parse(
                "
              struct ExtensionFieldSet {
                cluster_id clusterID = 0;
                AttributeValuePair attributeValueList[] = 1;
              }"
                .into(),
            ),
            Struct {
                struct_type: StructType::Regular,
                id: "ExtensionFieldSet",
                fields: vec![
                    StructField {
                        field: Field {
                            data_type: DataType::scalar("cluster_id"),
                            id: "clusterID",
                            code: 0,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: false,
                        is_fabric_sensitive: false,
                    },
                    StructField {
                        field: Field {
                            data_type: DataType::list_of("AttributeValuePair"),
                            id: "attributeValueList",
                            code: 1,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: false,
                        is_fabric_sensitive: false,
                    },
                ],
                is_fabric_scoped: false,
            },
        );
        assert_parse_ok(
            Struct::parse(
                "
                 request struct TestEventTriggerRequest {
                   octet_string<16> enableKey = 0;
                   int64u eventTrigger = 1;
                 }"
                .into(),
            ),
            Struct {
                struct_type: StructType::Request,
                id: "TestEventTriggerRequest",
                fields: vec![
                    StructField {
                        field: Field {
                            data_type: DataType::scalar_of_size("octet_string", 16),
                            id: "enableKey",
                            code: 0,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: false,
                        is_fabric_sensitive: false,
                    },
                    StructField {
                        field: Field {
                            data_type: DataType::scalar("int64u"),
                            id: "eventTrigger",
                            code: 1,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: false,
                        is_fabric_sensitive: false,
                    },
                ],
                is_fabric_scoped: false,
            },
        );

        assert_parse_ok(
            Struct::parse(
                "
                 response struct TimeSnapshotResponse = 2 {
                   systime_us systemTimeUs = 0;
                   nullable epoch_us UTCTimeUs = 1;
                 }"
                .into(),
            ),
            Struct {
                struct_type: StructType::Response(2),
                id: "TimeSnapshotResponse",
                fields: vec![
                    StructField {
                        field: Field {
                            data_type: DataType {
                                name: "systime_us",
                                is_list: false,
                                max_length: None,
                            },
                            id: "systemTimeUs",
                            code: 0,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: false,
                        is_fabric_sensitive: false,
                    },
                    StructField {
                        field: Field {
                            data_type: DataType {
                                name: "epoch_us",
                                is_list: false,
                                max_length: None,
                            },
                            id: "UTCTimeUs",
                            code: 1,
                        },
                        maturity: ApiMaturity::STABLE,
                        is_optional: false,
                        is_nullable: true,
                        is_fabric_sensitive: false,
                    },
                ],
                is_fabric_scoped: false,
            },
        );
    }

    #[test]
    fn test_parse_struct_field() {
        assert_parse_ok(
            StructField::parse("int8u sceneCount = 0;".into()),
            StructField {
                field: Field {
                    data_type: DataType::scalar("int8u"),
                    id: "sceneCount",
                    code: 0,
                },
                maturity: ApiMaturity::STABLE,
                is_optional: false,
                is_nullable: false,
                is_fabric_sensitive: false,
            },
        );
        assert_parse_ok(
            StructField::parse("fabric_sensitive int8u currentScene = 1;".into()),
            StructField {
                field: Field {
                    data_type: DataType::scalar("int8u"),
                    id: "currentScene",
                    code: 1,
                },
                maturity: ApiMaturity::STABLE,
                is_optional: false,
                is_nullable: false,
                is_fabric_sensitive: true,
            },
        );
        assert_parse_ok(
            StructField::parse(
                "optional nullable ExtensionFieldSet extensionFieldSets[] = 5;".into(),
            ),
            StructField {
                field: Field {
                    data_type: DataType::list_of("ExtensionFieldSet"),
                    id: "extensionFieldSets",
                    code: 5,
                },
                maturity: ApiMaturity::STABLE,
                is_optional: true,
                is_nullable: true,
                is_fabric_sensitive: false,
            },
        );
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
            api_maturity("123".into()),
            Ok(("123".into(), ApiMaturity::STABLE))
        );
        assert_eq!(
            remove_loc(api_maturity("stable abc".into())),
            Ok((" abc".into(), ApiMaturity::STABLE))
        );
        assert_eq!(
            remove_loc(api_maturity("provisional abc".into())),
            Ok((" abc".into(), ApiMaturity::PROVISIONAL))
        );
        assert_eq!(
            remove_loc(api_maturity("internal xyz".into())),
            Ok((" xyz".into(), ApiMaturity::INTERNAL))
        );
        assert_eq!(
            remove_loc(api_maturity("deprecated foobar".into())),
            Ok((" foobar".into(), ApiMaturity::DEPRECATED))
        );

        assert_eq!(
            remove_loc(api_maturity("DepreCAteD CaseTest".into())),
            Ok((" CaseTest".into(), ApiMaturity::DEPRECATED))
        );
    }

    #[test]
    fn test_hex_integer() {
        assert!(hex_integer("".into()).is_err());
        assert!(hex_integer("123".into()).is_err());
        assert!(hex_integer("0xzzz".into()).is_err());
        assert!(hex_integer("0x".into()).is_err());

        assert_eq!(
            remove_loc(hex_integer("0x12 abc".into())),
            Ok((" abc".into(), 0x12))
        );
        assert_eq!(
            remove_loc(hex_integer("0XABC XYZ".into())),
            Ok((" XYZ".into(), 0xABC))
        );
    }

    #[test]
    fn test_parse_decimal() {
        assert!(decimal_integer("a".into()).is_err());
        assert!(decimal_integer("".into()).is_err());

        assert_eq!(
            remove_loc(decimal_integer("123".into())),
            Ok(("".into(), 123))
        );
        assert_eq!(
            remove_loc(decimal_integer("1 2 3".into())),
            Ok((" 2 3".into(), 1))
        );
        assert_eq!(
            remove_loc(decimal_integer("0x123".into())),
            Ok(("x123".into(), 0))
        );
    }

    #[test]
    fn test_positive_integer() {
        assert!(positive_integer("a".into()).is_err());
        assert!(positive_integer("".into()).is_err());

        assert_eq!(
            remove_loc(positive_integer("123".into())),
            Ok(("".into(), 123))
        );
        assert_eq!(
            remove_loc(positive_integer("1 2 3".into())),
            Ok((" 2 3".into(), 1))
        );
        assert_eq!(
            remove_loc(positive_integer("0x123".into())),
            Ok(("".into(), 0x123))
        );
        assert_eq!(
            remove_loc(positive_integer("12ab".into())),
            Ok(("ab".into(), 12))
        );
        assert_eq!(
            remove_loc(positive_integer("0x12abcxyz".into())),
            Ok(("xyz".into(), 0x12abc))
        );
    }

    #[test]
    fn test_whitespace_group() {
        assert!(whitespace_group("a".into()).is_err());
        assert!(whitespace_group("".into()).is_err());

        assert_eq!(
            remove_loc(whitespace_group("   abc".into())),
            Ok(("abc".into(), Whitespace::Whitespace("   ")))
        );
        assert_eq!(
            remove_loc(whitespace_group("/* cpp comment */rest of text".into())),
            Ok((
                "rest of text".into(),
                Whitespace::CppComment(" cpp comment ")
            ))
        );
        assert_eq!(
            remove_loc(whitespace_group("/** Doc comment */rest of text".into())),
            Ok((
                "rest of text".into(),
                Whitespace::DocComment(" Doc comment ")
            ))
        );

        // only one (first) whitespace is removed
        assert_eq!(
            remove_loc(whitespace_group("//test   \nxyz".into())),
            Ok(("\nxyz".into(), Whitespace::CComment("test   ")))
        );
        assert_eq!(
            remove_loc(whitespace_group("  \n//test   \nxyz".into())),
            Ok(("//test   \nxyz".into(), Whitespace::Whitespace("  \n")))
        );
    }

    #[test]
    fn test_whitespace_group1() {
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
    fn test_whitespace_group0() {
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

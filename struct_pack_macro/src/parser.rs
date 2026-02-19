use nom::Parser;
use nom::{
    IResult,
    branch::alt,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt},
    multi::many0,
};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ByteOrder {
    Little,
    Big,
    Network,
    NativeUnaligned, // = format
    NativeAligned,   // @ format (default) - uses C struct alignment
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FormatKind {
    PadByte,          // x
    Char,             // c
    SignedByte,       // b
    UnsignedByte,     // B
    Bool,             // ?
    SignedShort,      // h
    UnsignedShort,    // H
    SignedInt,        // i
    UnsignedInt,      // I
    SignedLong,       // l
    UnsignedLong,     // L
    SignedLongLong,   // q
    UnsignedLongLong, // Q
    SignedSize,       // n
    UnsignedSize,     // N
    Half,             // e
    Float,            // f
    Double,           // d
    FloatComplex,     // F
    DoubleComplex,    // D
    Bytes,            // s
    PascalString,     // p
    Pointer,          // P
}

#[derive(Debug, Clone)]
pub struct FormatSpec {
    pub kind: FormatKind,
    pub count: usize,
}

// Parser functions using nom

/// Parse byte order character
fn parse_byte_order(input: &str) -> IResult<&str, ByteOrder> {
    alt((
        map(char('<'), |_| ByteOrder::Little),
        map(char('>'), |_| ByteOrder::Big),
        map(char('!'), |_| ByteOrder::Network),
        map(char('='), |_| ByteOrder::NativeUnaligned),
        map(char('@'), |_| ByteOrder::NativeAligned),
    ))
    .parse(input)
}

fn parse_format_kind<'a>(
    code: char,
    kind: FormatKind,
) -> impl Parser<&'a str, Output = FormatKind, Error = nom::error::Error<&'a str>> {
    map(char(code), move |_| kind)
}

/// Parse format character
fn parse_format_char(input: &str) -> IResult<&str, FormatKind> {
    alt([
        parse_format_kind('x', FormatKind::PadByte),
        parse_format_kind('c', FormatKind::Char),
        parse_format_kind('b', FormatKind::SignedByte),
        parse_format_kind('B', FormatKind::UnsignedByte),
        parse_format_kind('?', FormatKind::Bool),
        parse_format_kind('h', FormatKind::SignedShort),
        parse_format_kind('H', FormatKind::UnsignedShort),
        parse_format_kind('i', FormatKind::SignedInt),
        parse_format_kind('I', FormatKind::UnsignedInt),
        parse_format_kind('l', FormatKind::SignedLong),
        parse_format_kind('L', FormatKind::UnsignedLong),
        parse_format_kind('q', FormatKind::SignedLongLong),
        parse_format_kind('Q', FormatKind::UnsignedLongLong),
        parse_format_kind('n', FormatKind::SignedSize),
        parse_format_kind('N', FormatKind::UnsignedSize),
        parse_format_kind('e', FormatKind::Half),
        parse_format_kind('f', FormatKind::Float),
        parse_format_kind('d', FormatKind::Double),
        parse_format_kind('F', FormatKind::FloatComplex),
        parse_format_kind('D', FormatKind::DoubleComplex),
        parse_format_kind('s', FormatKind::Bytes),
        parse_format_kind('p', FormatKind::PascalString),
        parse_format_kind('P', FormatKind::Pointer),
    ])
    .parse(input)
}

/// Parse optional repeat count
fn parse_count(input: &str) -> IResult<&str, usize> {
    map_res(digit1, |s: &str| s.parse::<usize>()).parse(input)
}

/// Parse a single format specification
fn parse_format_spec(input: &str) -> IResult<&str, FormatSpec> {
    map(
        (opt(parse_count), parse_format_char),
        |(count_opt, kind)| {
            let count = count_opt.unwrap_or(1);
            FormatSpec { kind, count }
        },
    )
    .parse(input)
}

pub fn parse_format_string(fmt: &str) -> Result<(ByteOrder, Vec<FormatSpec>), String> {
    // Parse optional byte order
    let (rest, byte_order_opt) = opt(parse_byte_order)
        .parse(fmt)
        .map_err(|e| format!("Failed to parse byte order: {}", e))?;

    let byte_order = byte_order_opt.unwrap_or(ByteOrder::NativeAligned);

    // Parse format specs
    let (rest, specs) = many0(parse_format_spec)
        .parse(rest)
        .map_err(|e| format!("Failed to parse format specs: {}", e))?;

    if !rest.is_empty() {
        return Err(format!("Unexpected characters in format string: {}", rest));
    }

    Ok((byte_order, specs))
}

/// Get the size in bytes of a format type
pub fn get_type_size(kind: FormatKind) -> usize {
    match kind {
        FormatKind::PadByte => 1,
        FormatKind::Char => 1,
        FormatKind::SignedByte => 1,
        FormatKind::UnsignedByte => 1,
        FormatKind::Bool => 1,
        FormatKind::SignedShort => 2,
        FormatKind::UnsignedShort => 2,
        FormatKind::SignedInt => 4,
        FormatKind::UnsignedInt => 4,
        FormatKind::SignedLong => 4,
        FormatKind::UnsignedLong => 4,
        FormatKind::SignedLongLong => 8,
        FormatKind::UnsignedLongLong => 8,
        FormatKind::Float => 4,
        FormatKind::Double => 8,
        FormatKind::SignedSize | FormatKind::UnsignedSize | FormatKind::Pointer => {
            std::mem::size_of::<usize>()
        }
        FormatKind::Bytes => 1,        // per byte
        FormatKind::PascalString => 1, // per byte
        FormatKind::Half => 2,
        FormatKind::FloatComplex => 8,
        FormatKind::DoubleComplex => 16,
    }
}

/// Get the alignment requirement for a format type (for C struct alignment)
pub fn get_type_alignment(kind: FormatKind) -> usize {
    match kind {
        FormatKind::PadByte => 1,
        FormatKind::Char => 1,
        FormatKind::SignedByte => 1,
        FormatKind::UnsignedByte => 1,
        FormatKind::Bool => 1,
        FormatKind::SignedShort => 2,
        FormatKind::UnsignedShort => 2,
        FormatKind::SignedInt => 4,
        FormatKind::UnsignedInt => 4,
        FormatKind::SignedLong => 4,
        FormatKind::UnsignedLong => 4,
        FormatKind::SignedLongLong => 8,
        FormatKind::UnsignedLongLong => 8,
        FormatKind::Float => 4,
        FormatKind::Double => 8,
        FormatKind::SignedSize | FormatKind::UnsignedSize | FormatKind::Pointer => {
            std::mem::size_of::<usize>()
        }
        FormatKind::Bytes => 1,
        FormatKind::PascalString => 1,
        FormatKind::Half => 2,
        FormatKind::FloatComplex => 4,  // Align to float
        FormatKind::DoubleComplex => 8, // Align to double
    }
}

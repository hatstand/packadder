use nom::Parser;
use proc_macro::TokenStream;
use proc_macro_error::{abort_call_site, proc_macro_error};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, LitStr, Token, parse_macro_input};

use nom::{
    IResult,
    branch::alt,
    character::complete::{char, digit1},
    combinator::{map, map_res, opt},
    multi::many0,
    sequence::tuple,
};

struct PackArgs {
    format: LitStr,
    values: Vec<Expr>,
}

impl Parse for PackArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let format: LitStr = input.parse()?;
        let mut values = Vec::new();

        while !input.is_empty() {
            input.parse::<Token![,]>()?;
            if input.is_empty() {
                break;
            }
            values.push(input.parse()?);
        }

        Ok(PackArgs { format, values })
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum ByteOrder {
    Little,
    Big,
    Network,
    Native,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormatKind {
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
struct FormatSpec {
    kind: FormatKind,
    count: usize,
}

// Parser functions using nom

/// Parse byte order character
fn parse_byte_order(input: &str) -> IResult<&str, ByteOrder> {
    alt((
        map(char('<'), |_| ByteOrder::Little),
        map(char('>'), |_| ByteOrder::Big),
        map(char('!'), |_| ByteOrder::Network),
        map(char('='), |_| ByteOrder::Native),
        map(char('@'), |_| ByteOrder::Native),
    ))
    .parse(input)
}

/// Parse format character
fn parse_format_char(input: &str) -> IResult<&str, char> {
    alt([
        char('x'),
        char('c'),
        char('b'),
        char('B'),
        char('?'),
        char('h'),
        char('H'),
        char('i'),
        char('I'),
        char('l'),
        char('L'),
        char('q'),
        char('Q'),
        char('n'),
        char('N'),
        char('f'),
        char('d'),
        char('e'),
        char('F'),
        char('D'),
        char('s'),
        char('p'),
        char('P'),
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
        tuple((opt(parse_count), parse_format_char)),
        |(count_opt, format_char)| {
            let count = count_opt.unwrap_or(1);
            let kind = match format_char {
                'x' => FormatKind::PadByte,
                'c' => FormatKind::Char,
                'b' => FormatKind::SignedByte,
                'B' => FormatKind::UnsignedByte,
                '?' => FormatKind::Bool,
                'h' => FormatKind::SignedShort,
                'H' => FormatKind::UnsignedShort,
                'i' => FormatKind::SignedInt,
                'I' => FormatKind::UnsignedInt,
                'l' => FormatKind::SignedLong,
                'L' => FormatKind::UnsignedLong,
                'q' => FormatKind::SignedLongLong,
                'Q' => FormatKind::UnsignedLongLong,
                'n' => FormatKind::SignedSize,
                'N' => FormatKind::UnsignedSize,
                'e' => FormatKind::Half,
                'f' => FormatKind::Float,
                'd' => FormatKind::Double,
                'F' => FormatKind::FloatComplex,
                'D' => FormatKind::DoubleComplex,
                's' => FormatKind::Bytes,
                'p' => FormatKind::PascalString,
                'P' => FormatKind::Pointer,
                _ => unreachable!("Unknown format character: {}", format_char),
            };
            FormatSpec { kind, count }
        },
    )
    .parse(input)
}

fn parse_format_string(fmt: &str) -> Result<(ByteOrder, Vec<FormatSpec>), String> {
    // Parse optional byte order
    let (rest, byte_order_opt) = opt(parse_byte_order)
        .parse(fmt)
        .map_err(|e| format!("Failed to parse byte order: {}", e))?;

    let byte_order = byte_order_opt.unwrap_or(ByteOrder::Native);

    // Parse format specs
    let (rest, specs) = many0(parse_format_spec)
        .parse(rest)
        .map_err(|e| format!("Failed to parse format specs: {}", e))?;

    if !rest.is_empty() {
        return Err(format!("Unexpected characters in format string: {}", rest));
    }

    Ok((byte_order, specs))
}

fn format_spec_to_rust_type(spec: &FormatSpec) -> proc_macro2::TokenStream {
    match spec.kind {
        FormatKind::Char => quote! { u8 },
        FormatKind::SignedByte => quote! { i8 },
        FormatKind::UnsignedByte => quote! { u8 },
        FormatKind::SignedShort => quote! { i16 },
        FormatKind::UnsignedShort => quote! { u16 },
        FormatKind::SignedInt | FormatKind::SignedLong => quote! { i32 },
        FormatKind::UnsignedInt | FormatKind::UnsignedLong => quote! { u32 },
        FormatKind::SignedLongLong => quote! { i64 },
        FormatKind::UnsignedLongLong => quote! { u64 },
        FormatKind::SignedSize => quote! { isize },
        FormatKind::UnsignedSize => quote! { usize },
        FormatKind::Float => quote! { f32 },
        FormatKind::Double => quote! { f64 },
        FormatKind::Bytes => quote! { &[u8] },
        FormatKind::Bool => quote! { bool },
        _ => {
            abort_call_site!("Unsupported format kind for type mapping: {:?}", spec.kind)
        }
    }
}

fn generate_pack_code(
    byte_order: ByteOrder,
    spec: &FormatSpec,
    value: &Expr,
) -> proc_macro2::TokenStream {
    // Handle bytes (string) format
    if spec.kind == FormatKind::Bytes {
        let count = spec.count;
        return quote! {
            {
                let bytes: &[u8] = #value;
                let len = bytes.len().min(#count);
                result.extend_from_slice(&bytes[..len]);
                // Pad with zeros if needed
                for _ in len..#count {
                    result.push(0);
                }
            }
        };
    }

    // Single-byte types don't need endianness
    match spec.kind {
        FormatKind::Char => {
            return quote! {
                result.write_u8(#value).unwrap();
            };
        }
        FormatKind::SignedByte => {
            return quote! {
                result.write_i8(#value).unwrap();
            };
        }
        FormatKind::UnsignedByte => {
            return quote! {
                result.write_u8(#value).unwrap();
            };
        }
        FormatKind::Bool => {
            return quote! {
                result.write_u8(if #value { 1 } else { 0 }).unwrap();
            };
        }
        _ => {}
    }

    // ssize_t & size_t are always native-endian.
    match spec.kind {
        FormatKind::SignedSize => {
            // Handle size_t and ssize_t based on target pointer width
            #[cfg(target_pointer_width = "64")]
            {
                return quote! {
                    result.write_i64::<byteorder::NativeEndian>(#value as i64).unwrap();
                };
            }
            #[cfg(target_pointer_width = "32")]
            {
                return quote! {
                    result.write_i32::<byteorder::NativeEndian>(#value as i32).unwrap();
                };
            }
        }
        FormatKind::UnsignedSize => {
            #[cfg(target_pointer_width = "64")]
            {
                return quote! {
                    result.write_u64::<byteorder::NativeEndian>(#value as u64).unwrap();
                };
            }
            #[cfg(target_pointer_width = "32")]
            {
                return quote! {
                    result.write_u32::<byteorder::NativeEndian>(#value as u32).unwrap();
                };
            }
        }
        _ => {}
    }

    let write_method = match spec.kind {
        FormatKind::SignedShort => quote! { write_i16 },
        FormatKind::UnsignedShort => quote! { write_u16 },
        FormatKind::SignedInt | FormatKind::SignedLong => quote! { write_i32 },
        FormatKind::UnsignedInt | FormatKind::UnsignedLong => quote! { write_u32 },
        FormatKind::SignedLongLong => quote! { write_i64 },
        FormatKind::UnsignedLongLong => quote! { write_u64 },
        FormatKind::Float => quote! { write_f32 },
        FormatKind::Double => quote! { write_f64 },
        _ => {
            panic!("Cannot generate pack code for pad byte or bytes")
        }
    };

    match byte_order {
        ByteOrder::Big | ByteOrder::Network => {
            quote! {
                result.#write_method::<byteorder::BigEndian>(#value).unwrap();
            }
        }
        ByteOrder::Little => {
            quote! {
                result.#write_method::<byteorder::LittleEndian>(#value).unwrap();
            }
        }
        ByteOrder::Native => {
            quote! {
                result.#write_method::<byteorder::NativeEndian>(#value).unwrap();
            }
        }
    }
}

#[proc_macro_error]
#[proc_macro]
pub fn pack(input: TokenStream) -> TokenStream {
    let PackArgs { format, values } = parse_macro_input!(input as PackArgs);

    let format_str = format.value();
    let (byte_order, specs) = match parse_format_string(&format_str) {
        Ok(result) => result,
        Err(e) => {
            return syn::Error::new_spanned(format, e).to_compile_error().into();
        }
    };

    // Calculate total number of values needed (accounting for repeat counts)
    // Pad bytes ('x') don't consume values
    // Bytes ('s') consume 1 value regardless of count
    let total_values_needed: usize = specs
        .iter()
        .map(|s| match s.kind {
            FormatKind::PadByte => 0,
            FormatKind::Bytes => 1,
            FormatKind::Char => s.count,
            _ => s.count,
        })
        .sum();

    // Handle empty format string
    if total_values_needed == 0 && values.is_empty() {
        // Still might have pad bytes
        let mut pack_operations = Vec::new();
        for spec in &specs {
            if spec.kind == FormatKind::PadByte {
                let count = spec.count;
                pack_operations.push(quote! {
                    for _ in 0..#count {
                        result.push(0);
                    }
                });
            }
        }

        return TokenStream::from(quote! {
            {
                let mut result = Vec::new();
                #(#pack_operations)*
                Ok::<Vec<u8>, anyhow::Error>(result)
            }
        });
    }

    if values.len() != total_values_needed {
        let error_msg = format!(
            "Format string '{}' expects {} value(s) but {} were provided",
            format_str,
            total_values_needed,
            values.len()
        );
        return syn::Error::new_spanned(format, error_msg)
            .to_compile_error()
            .into();
    }

    // Generate type assertions and packing code
    let mut type_checks = Vec::new();
    let mut pack_operations = Vec::new();
    let mut value_idx = 0;

    for spec in &specs {
        if spec.kind == FormatKind::PadByte {
            // Pad bytes - no value needed, just add zeros
            let count = spec.count;
            pack_operations.push(quote! {
                for _ in 0..#count {
                    result.push(0);
                }
            });
        } else if spec.kind == FormatKind::Bytes {
            // Bytes format - consumes 1 value regardless of count
            if value_idx >= values.len() {
                break;
            }

            let value = &values[value_idx];
            let rust_type = format_spec_to_rust_type(spec);

            // Generate compile-time type check
            type_checks.push(quote! {
                let _: #rust_type = #value;
            });

            // Generate packing code
            let pack_code = generate_pack_code(byte_order, spec, value);
            pack_operations.push(pack_code);

            value_idx += 1;
        } else {
            let rust_type = format_spec_to_rust_type(spec);

            for _ in 0..spec.count {
                if value_idx >= values.len() {
                    break;
                }

                let value = &values[value_idx];

                // Generate compile-time type check
                type_checks.push(quote! {
                    let _: #rust_type = #value;
                });

                // Generate packing code
                let pack_code = generate_pack_code(byte_order, spec, value);
                pack_operations.push(pack_code);

                value_idx += 1;
            }
        }
    }

    let expanded = quote! {
        {
            use byteorder::WriteBytesExt;
            #(#type_checks)*
            let mut result = Vec::new();
            #(#pack_operations)*
            Ok::<Vec<u8>, anyhow::Error>(result)
        }
    };

    TokenStream::from(expanded)
}

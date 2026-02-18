use proc_macro::TokenStream;
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

#[derive(Debug, Clone)]
struct FormatSpec {
    format_char: char,
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
    ))(input)
}

/// Parse format character
fn parse_format_char(input: &str) -> IResult<&str, char> {
    alt((
        char('b'),
        char('B'),
        char('h'),
        char('H'),
        char('i'),
        char('I'),
        char('q'),
        char('Q'),
        char('f'),
        char('d'),
        char('x'),
        char('s'),
    ))(input)
}

/// Parse optional repeat count
fn parse_count(input: &str) -> IResult<&str, usize> {
    map_res(digit1, |s: &str| s.parse::<usize>())(input)
}

/// Parse a single format specification
fn parse_format_spec(input: &str) -> IResult<&str, FormatSpec> {
    map(
        tuple((opt(parse_count), parse_format_char)),
        |(count, format_char)| FormatSpec {
            count: count.unwrap_or(1),
            format_char,
        },
    )(input)
}

fn parse_format_string(fmt: &str) -> Result<(ByteOrder, Vec<FormatSpec>), String> {
    // Parse optional byte order
    let (rest, byte_order_opt) =
        opt(parse_byte_order)(fmt).map_err(|e| format!("Failed to parse byte order: {}", e))?;

    let byte_order = byte_order_opt.unwrap_or(ByteOrder::Native);

    // Parse format specs
    let (rest, specs) = many0(parse_format_spec)(rest)
        .map_err(|e| format!("Failed to parse format specs: {}", e))?;

    if !rest.is_empty() {
        return Err(format!("Unexpected characters in format string: {}", rest));
    }

    // Validate format characters
    for spec in &specs {
        match spec.format_char {
            'b' | 'B' | 'h' | 'H' | 'i' | 'I' | 'q' | 'Q' | 'f' | 'd' | 'x' => {}
            's' => {
                return Err("Format character 's' (string) not yet supported".to_string());
            }
            _ => {
                return Err(format!("Unknown format character: {}", spec.format_char));
            }
        }
    }

    Ok((byte_order, specs))
}

fn format_char_to_rust_type(ch: char) -> proc_macro2::TokenStream {
    match ch {
        'b' => quote! { i8 },
        'B' => quote! { u8 },
        'h' => quote! { i16 },
        'H' => quote! { u16 },
        'i' => quote! { i32 },
        'I' => quote! { u32 },
        'q' => quote! { i64 },
        'Q' => quote! { u64 },
        'f' => quote! { f32 },
        'd' => quote! { f64 },
        _ => panic!("Unknown format character: {}", ch),
    }
}

fn generate_pack_code(byte_order: ByteOrder, ch: char, value: &Expr) -> proc_macro2::TokenStream {
    match byte_order {
        ByteOrder::Big | ByteOrder::Network => {
            quote! { result.extend((#value).to_be_bytes()); }
        }
        ByteOrder::Little => {
            quote! { result.extend((#value).to_le_bytes()); }
        }
        ByteOrder::Native => {
            quote! { result.extend((#value).to_ne_bytes()); }
        }
    }
}

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
    let total_values_needed: usize = specs
        .iter()
        .filter(|s| s.format_char != 'x')
        .map(|s| s.count)
        .sum();

    // Handle empty format string
    if total_values_needed == 0 && values.is_empty() {
        // Still might have pad bytes
        let mut pack_operations = Vec::new();
        for spec in &specs {
            if spec.format_char == 'x' {
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
        if spec.format_char == 'x' {
            // Pad bytes - no value needed, just add zeros
            let count = spec.count;
            pack_operations.push(quote! {
                for _ in 0..#count {
                    result.push(0);
                }
            });
            continue;
        }

        let rust_type = format_char_to_rust_type(spec.format_char);

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
            let pack_code = generate_pack_code(byte_order, spec.format_char, value);
            pack_operations.push(pack_code);

            value_idx += 1;
        }
    }

    let expanded = quote! {
        {
            #(#type_checks)*
            let mut result = Vec::new();
            #(#pack_operations)*
            Ok::<Vec<u8>, anyhow::Error>(result)
        }
    };

    TokenStream::from(expanded)
}

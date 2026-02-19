use proc_macro::TokenStream;
use proc_macro_error::{abort_call_site, proc_macro_error};
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{Expr, LitStr, Token, parse_macro_input};

mod parser;
use parser::{
    ByteOrder, FormatKind, FormatSpec, get_type_alignment, get_type_size, parse_format_string,
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
        FormatKind::PascalString => quote! { &[u8]},
        FormatKind::Pointer => quote! { *const _ },
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
    match spec.kind {
        FormatKind::Bytes => {
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
        FormatKind::PascalString => {
            let count = spec.count;
            if count > 256 {
                abort_call_site!(
                    "Pascal string count must be in range 0..=256, but got {}",
                    count
                );
            }
            return quote! {
                {
                    // Pascal string:
                    // Length-prefixed string where `#count` is the _total_ length including the prefix.
                    let len_prefix = min(#count - 1, 255) as u8;
                    let bytes: &[u8] = #value;

                    let mut output_bytes = bytes[..min(bytes.len(), (len_prefix as usize))].to_vec();
                    output_bytes.extend(vec![0; #count - 1 - output_bytes.len()]); // Pad with zeros if needed

                    assert_eq!(output_bytes.len(), #count - 1);

                    result.write_u8(len_prefix)?;
                    result.extend(output_bytes);
                }
            };
        }
        _ => {}
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

    // ssize_t, size_t and pointers are always native-endian.
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
        FormatKind::Pointer => {
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
            abort_call_site!("Unsupported format kind for packing: {:?}", spec.kind)
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
        ByteOrder::NativeUnaligned | ByteOrder::NativeAligned => {
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
            FormatKind::PascalString => 1,
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
                Ok::<Vec<u8>, anyhow::Error>(Vec::new())
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

    // Track current offset for alignment calculations (only used with NativeAligned)
    let needs_alignment = byte_order == ByteOrder::NativeAligned;

    if needs_alignment {
        // Add offset tracking at runtime
        pack_operations.push(quote! {
            let mut __offset: usize = 0;
        });
    }

    for spec in &specs {
        // Insert alignment padding if needed (for @ format)
        if needs_alignment && spec.kind != FormatKind::PadByte {
            let alignment = get_type_alignment(spec.kind);
            pack_operations.push(quote! {
                // Align to the type's alignment requirement
                let desired_alignment = #alignment;
                let current_alignment = __offset % desired_alignment;
                let padding = if current_alignment == 0 { 0 } else { desired_alignment - current_alignment };
                for _ in 0..padding {
                    result.push(0);
                }
                __offset = __offset.wrapping_add(padding);
            });
        }

        if spec.kind == FormatKind::PadByte {
            // Pad bytes - no value needed, just add zeros
            let count = spec.count;
            pack_operations.push(quote! {
                for _ in 0..#count {
                    result.push(0);
                }
            });
            if needs_alignment {
                pack_operations.push(quote! {
                    __offset = __offset.wrapping_add(#count);
                });
            }
        } else if spec.kind == FormatKind::Bytes || spec.kind == FormatKind::PascalString {
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

            // Track offset for alignment
            if needs_alignment {
                let size = spec.count; // For Bytes/PascalString, count is the total size
                pack_operations.push(quote! {
                    __offset = __offset.wrapping_add(#size);
                });
            }

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

                // Track offset for alignment
                if needs_alignment {
                    let size = get_type_size(spec.kind);
                    pack_operations.push(quote! {
                        __offset = __offset.wrapping_add(#size);
                    });
                }

                value_idx += 1;
            }
        }
    }

    let expanded = quote! {
        {
            use byteorder::WriteBytesExt;
            use std::cmp::min;
            #(#type_checks)*
            let mut result = Vec::new();
            #(#pack_operations)*
            Ok::<Vec<u8>, anyhow::Error>(result)
        }
    };

    TokenStream::from(expanded)
}

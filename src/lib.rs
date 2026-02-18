//! Rust port of Python's `struct.pack()` functionality
//!
//! This module provides a way to pack values into bytes according to a format string,
//! similar to Python's struct module. The format string is parsed using nom and values
//! are packed using a type-safe HList-based API.
//!
//! # Format String Syntax
//!
//! Format strings consist of:
//! - Optional byte order/size/alignment character:
//!   - `<` - little-endian
//!   - `>` - big-endian
//!   - `!` - network (big-endian)
//!   - `=` - native byte order
//!   - `@` - native byte order with native alignment (default)
//! - Format characters (optionally preceded by a repeat count):
//!   - `b` - signed byte (i8)
//!   - `B` - unsigned byte (u8)
//!   - `h` - signed short (i16)
//!   - `H` - unsigned short (u16)
//!   - `i` - signed int (i32)
//!   - `I` - unsigned int (u32)
//!   - `q` - signed long long (i64)
//!   - `Q` - unsigned long long (u64)
//!   - `f` - float (f32)
//!   - `d` - double (f64)
//!   - `s` - bytes (requires count)
//!   - `x` - pad byte
//!
//! # Examples
//!
//! ```
//!
//! // Type-safe packing.
//! use packadder::pack;
//! let bytes = pack!(">HHI", 1u16, 2u16, 0x12345678u32)?;
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! # Testing
//!
//! This module includes comprehensive compatibility tests that verify the Rust implementation
//! matches Python's `struct.pack()` exactly. These tests use pyo3 to call Python and compare
//! results byte-for-byte.
//!
//! To run the compatibility tests:
//! ```bash
//! cargo test python_compat
//! ```
//!
//! Note: These tests require Python to be installed with pyo3 support.

/// Variadic pack! macro with compile-time type checking
///
/// This macro parses the format string at compile time and generates code that enforces
/// the exact types required by each format character.
///
/// # Examples
///
/// ```
/// use packadder::pack;
///
/// // Type-safe packing with compile-time verification
/// let bytes = pack!(">HHI", 1u16, 2u16, 0x12345678u32)?;
/// assert_eq!(bytes.len(), 8);
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// Empty format strings are supported:
/// ```
/// use packadder::pack;
///
/// let bytes = pack!("")?;
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// # Repeat Counts
/// Format strings support repeat counts (e.g., "3B" means 3 unsigned bytes):
/// ```
/// use packadder::pack;
/// let bytes = pack!("3B", 1u8, 2u8, 3u8)?;
/// assert_eq!(bytes, vec![1, 2, 3]);
///
/// // Mix repeat counts with regular formats
/// let bytes = pack!(">2HI", 1u16, 2u16, 0x12345678u32)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// # Type Safety
/// The macro provides compile-time type checking:
///
/// ```compile_fail
/// use packadder::pack;
/// // This fails at compile time: u32 doesn't match format 'H' (u16)
/// let bytes = pack!(">H", 0x12345678u32)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// ```compile_fail
/// use packadder::pack;
/// // This fails at compile time: not enough values
/// let bytes = pack!(">HH", 1u16)?;
/// # Ok::<(), anyhow::Error>(())
/// ```
// Re-export the procedural macro
pub use struct_pack_macro::pack;

#[cfg(test)]
mod tests {
    use super::*;

    use anyhow::Result;

    #[test]
    fn test_pack_tuple() -> Result<()> {
        let bytes = pack!(">HHI", 1u16, 2u16, 0x12345678u32)?;
        assert_eq!(bytes, vec![0, 1, 0, 2, 0x12, 0x34, 0x56, 0x78]);
        Ok(())
    }

    #[test]
    fn test_pack_multiple_types() -> Result<()> {
        let bytes = pack!("<BHI", 0x42u8, 0x1234u16, 0x56789ABCu32)?;
        assert_eq!(bytes, vec![0x42, 0x34, 0x12, 0xBC, 0x9A, 0x78, 0x56]);
        Ok(())
    }

    #[test]
    fn test_pack_with_signed() -> Result<()> {
        let bytes = pack!(">bhi", -1i8, -256i16, 1000i32)?;
        assert_eq!(bytes, vec![0xFF, 0xFF, 0x00, 0x00, 0x00, 0x03, 0xE8]);
        Ok(())
    }

    #[test]
    fn test_pack_floats() -> Result<()> {
        let bytes = pack!("<fd", 3.14f32, 2.718f64)?;
        assert_eq!(bytes.len(), 4 + 8); // 4 bytes for f32, 8 for f64
        Ok(())
    }

    #[test]
    fn test_pack_repeat_count() -> Result<()> {
        let bytes = pack!("3B", 1u8, 2u8, 3u8)?;
        assert_eq!(bytes, vec![1, 2, 3]);
        Ok(())
    }

    #[test]
    fn test_pack_repeat_count_mixed() -> Result<()> {
        // Mix repeat counts with regular formats
        let bytes = pack!(">2HI", 1u16, 2u16, 0x12345678u32)?;
        assert_eq!(bytes, vec![0, 1, 0, 2, 0x12, 0x34, 0x56, 0x78]);
        Ok(())
    }

    #[test]
    fn test_pack_multiple_repeat_counts() -> Result<()> {
        // Multiple repeat counts in one format
        let bytes = pack!("<2B3H", 10u8, 20u8, 100u16, 200u16, 300u16)?;
        assert_eq!(
            bytes,
            vec![
                10, 20, // 2B
                100, 0, 200, 0, 44, 1, // 3H (300 = 0x012C)
            ]
        );
        Ok(())
    }

    #[test]
    fn test_pack_empty() -> Result<()> {
        let bytes = pack!("")?;
        assert_eq!(bytes, Vec::<u8>::new());
        Ok(())
    }

    // Type mismatch and missing values are caught at compile time
    // See doc tests on the pack! macro for compile_fail examples

    #[test]
    fn test_pack_five_values() -> Result<()> {
        let bytes = pack!(">BHBIB", 1u8, 2u16, 3u8, 4u32, 5u8)?;
        assert_eq!(bytes, vec![1, 0, 2, 3, 0, 0, 0, 4, 5]);
        Ok(())
    }
}

#[cfg(test)]
mod python_compat_tests {
    //! Python compatibility tests
    //!
    //! These tests verify that our Rust implementation matches Python's struct.pack()
    //! by calling Python via pyo3 and comparing outputs.
    //!
    //! To run these tests, you need Python with the struct module available (standard library).
    //! Run with: `cargo test python_compat`

    use super::*;
    use anyhow::Result;
    use pyo3::prelude::*;
    use pyo3::types::PyBytes;

    /// Helper function to call Python's struct.pack
    fn python_pack(format: &str, values: Vec<&dyn ToPyObject>) -> Vec<u8> {
        Python::with_gil(|py| {
            let struct_module = py.import_bound("struct").unwrap();
            let pack_fn = struct_module.getattr("pack").unwrap();

            // Build args tuple: (format, *values)
            let mut args = vec![format.to_object(py)];
            for value in values {
                args.push(value.to_object(py));
            }

            let result = pack_fn
                .call1(pyo3::types::PyTuple::new_bound(py, args))
                .unwrap();
            let bytes: &Bound<'_, PyBytes> = result.downcast().unwrap();
            bytes.as_bytes().to_vec()
        })
    }

    /// Macro to simplify compatibility tests
    macro_rules! test_compat {
        ($name:ident, $format:expr, $py_values:expr) => {
            #[test]
            fn $name() -> Result<()> {
                let rust_result = pack!($format)?;
                let py_result = python_pack($format, $py_values);
                assert_eq!(
                    rust_result, py_result,
                    "Mismatch for format '{}': Rust={:?}, Python={:?}",
                    $format, rust_result, py_result
                );
                Ok(())
            }
        };
        ($name:ident, $format:expr, $py_values:expr, $($val:expr),+) => {
            #[test]
            fn $name() -> Result<()> {
                let rust_result = pack!($format, $($val),+)?;
                let py_result = python_pack($format, $py_values);
                assert_eq!(
                    rust_result, py_result,
                    "Mismatch for format '{}': Rust={:?}, Python={:?}",
                    $format, rust_result, py_result
                );
                Ok(())
            }
        };
    }

    // Basic type tests
    test_compat!(
        test_compat_unsigned_int_little_endian,
        "<I",
        vec![&0x12345678u32],
        0x12345678u32
    );

    test_compat!(
        test_compat_unsigned_int_big_endian,
        ">I",
        vec![&0x12345678u32],
        0x12345678u32
    );

    test_compat!(test_compat_signed_byte, "b", vec![&-42i8], -42i8);

    test_compat!(test_compat_unsigned_byte, "B", vec![&255u8], 255u8);

    test_compat!(
        test_compat_signed_short_little_endian,
        "<h",
        vec![&-1000i16],
        -1000i16
    );

    test_compat!(
        test_compat_unsigned_short_big_endian,
        ">H",
        vec![&0x1234u16],
        0x1234u16
    );

    test_compat!(
        test_compat_signed_int_little_endian,
        "<i",
        vec![&-100000i32],
        -100000i32
    );

    test_compat!(
        test_compat_unsigned_int_network_order,
        "!I",
        vec![&0xDEADBEEFu32],
        0xDEADBEEFu32
    );

    test_compat!(
        test_compat_signed_long_long_little_endian,
        "<q",
        vec![&-9223372036854775807i64],
        -9223372036854775807i64
    );

    test_compat!(
        test_compat_unsigned_long_long_big_endian,
        ">Q",
        vec![&0x123456789ABCDEFu64],
        0x123456789ABCDEFu64
    );

    test_compat!(
        test_compat_float_little_endian,
        "<f",
        vec![&3.14159f32],
        3.14159f32
    );

    test_compat!(
        test_compat_double_big_endian,
        ">d",
        vec![&2.718281828459045f64],
        2.718281828459045f64
    );

    test_compat!(
        test_compat_multiple_values_mixed,
        ">BHI",
        vec![&0x42u8, &0x1234u16, &0x56789ABCu32],
        0x42u8,
        0x1234u16,
        0x56789ABCu32
    );

    test_compat!(
        test_compat_three_unsigned_shorts,
        "<HHH",
        vec![&1u16, &2u16, &3u16],
        1u16,
        2u16,
        3u16
    );

    test_compat!(
        test_compat_signed_values,
        ">bhi",
        vec![&-1i8, &-256i16, &1000i32],
        -1i8,
        -256i16,
        1000i32
    );

    test_compat!(
        test_compat_five_values,
        ">BHBIB",
        vec![&1u8, &2u16, &3u8, &4u32, &5u8],
        1u8,
        2u16,
        3u8,
        4u32,
        5u8
    );

    test_compat!(
        test_compat_repeat_count,
        "3B",
        vec![&0x10u8, &0x20u8, &0x30u8],
        0x10u8,
        0x20u8,
        0x30u8
    );

    test_compat!(
        test_compat_native_byte_order,
        "=I",
        vec![&0x12345678u32],
        0x12345678u32
    );

    test_compat!(
        test_compat_complex_format,
        "<BhHiIqQ",
        vec![
            &0x12u8,
            &-1000i16,
            &5000u16,
            &-100000i32,
            &0xDEADBEEFu32,
            &-9223372036854775807i64,
            &0x123456789ABCDEFu64,
        ],
        0x12u8,
        -1000i16,
        5000u16,
        -100000i32,
        0xDEADBEEFu32,
        -9223372036854775807i64,
        0x123456789ABCDEFu64
    );

    test_compat!(
        test_compat_floats_and_ints,
        "<fbdI",
        vec![&3.14f32, &-42i8, &2.718f64, &0x12345678u32],
        3.14f32,
        -42i8,
        2.718f64,
        0x12345678u32
    );

    test_compat!(
        test_compat_edge_case_zero,
        ">IHB",
        vec![&0u32, &0u16, &0u8],
        0u32,
        0u16,
        0u8
    );

    test_compat!(
        test_compat_negative_numbers,
        "<bhiq",
        vec![
            &-128i8,
            &-32768i16,
            &-2147483648i32,
            &-9223372036854775808i64
        ],
        -128i8,
        -32768i16,
        -2147483648i32,
        -9223372036854775808i64
    );

    #[test]
    fn test_compat_edge_case_max_values() -> Result<()> {
        // Multiple assertions in one test
        let rust_result = pack!("B", 255u8)?;
        let py_result = python_pack("B", vec![&255u8]);
        assert_eq!(rust_result, py_result);

        let rust_result = pack!(">H", 65535u16)?;
        let py_result = python_pack(">H", vec![&65535u16]);
        assert_eq!(rust_result, py_result);

        let rust_result = pack!(">I", 0xFFFFFFFFu32)?;
        let py_result = python_pack(">I", vec![&0xFFFFFFFFu32]);
        assert_eq!(rust_result, py_result);

        Ok(())
    }
}

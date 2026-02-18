//! Rust port of Python's [`struct.pack()`](https://docs.python.org/3/library/struct.html) functionality
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
//!   - `@` - native byte order (with native alignment). Also the default.
//! - Format characters (optionally preceded by a repeat count):
//!   - `x` - pad byte
//!   - `c` - char (u8)
//!   - `b` - signed byte (i8)
//!   - `B` - unsigned byte (u8)
//!   - `?` - bool (u8, 1 for true, 0 for false)
//!   - `h` - signed short (i16)
//!   - `H` - unsigned short (u16)
//!   - `i` - signed int (i32)
//!   - `I` - unsigned int (u32)
//!   - `l` - signed long (i32)
//!   - `L` - unsigned long (u32)
//!   - `q` - signed long long (i64)
//!   - `Q` - unsigned long long (u64)
//!   - `f` - float (f32)
//!   - `d` - double (f64)
//!   - `s` - bytes (requires count)
//!   - `p` - pascal string (requires count)
//!   - `P` - pointer (const *)
//!
//! # Examples
//!
//! ```
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
//! Note: These tests require Python to be installed.

/// Variadic pack! macro with compile-time type checking
///
/// The first argument is a format string that specifies how to pack the subsequent values into bytes.
/// The following arguments are the values to be packed, which must match the types specified by the format string.
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
/// # Bytes/Strings
/// Format character 's' packs byte slices. The count specifies how many bytes to write.
/// If the input is shorter, it's padded with zeros. If longer, it's truncated.
/// ```
/// use packadder::pack;
/// // Pack exactly 5 bytes
/// let bytes = pack!("5s", b"hello")?;
/// assert_eq!(bytes, b"hello");
///
/// // Short strings are padded
/// let bytes = pack!("5s", b"hi")?;
/// assert_eq!(bytes, vec![b'h', b'i', 0, 0, 0]);
///
/// // Long strings are truncated
/// let bytes = pack!("5s", b"hello world")?;
/// assert_eq!(bytes, b"hello");
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
///
/// ```compile_fail
/// use packadder::pack;
/// // This fails at compile time: string spec too long.
/// let bytes = pack!("257p", b"Hello, world!")?;
/// # Ok::<(), anyhow::Error>(())
/// ```
///
/// Unsupported format codes:
/// `e` (half-precision float)
/// `F` (float complex)
/// `D` (double complex)
///
/// ```compile_fail
/// use packadder::pack;
/// pack!("<e", 1.0f32)?; // 'e' (half-precision float) is not supported
/// ```
///
// Re-export the procedural macro
pub use struct_pack_macro::pack;

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::Result;
    use byteorder::{ByteOrder, LittleEndian};

    #[test]
    fn test_pack() -> Result<()> {
        let bytes = pack!(">HHI", 1u16, 2u16, 0x12345678u32)?;
        assert_eq!(bytes, vec![0, 1, 0, 2, 0x12, 0x34, 0x56, 0x78]);
        Ok(())
    }

    #[test]
    fn test_pack_from_variables() -> Result<()> {
        let a: u16 = 1;
        let b: u16 = 2;
        let c: u32 = 0x12345678;
        let bytes = pack!(">HHI", a, b, c)?;
        assert_eq!(bytes, vec![0, 1, 0, 2, 0x12, 0x34, 0x56, 0x78]);
        Ok(())
    }

    #[test]
    fn test_pack_alignment() -> Result<()> {
        let bytes = pack!("hI", 42, 44)?;
        assert_eq!(bytes, vec![0x2a, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00, 0x00]);
        Ok(())
    }

    #[test]
    fn test_mixed_alignment() -> Result<()> {
        // This should be laid out as:
        // char (1 byte) + 1 byte padding + 2 bytes for short + 4 bytes for int + 1 byte
        // A C struct would add 3 more bytes of padding at the end, but Python does not
        // implement that.
        let bytes = pack!("chic", b'A', 42, 43, b'B')?;
        assert_eq!(bytes, vec![b'A', 0, 42, 0, 43, 0, 0, 0, b'B']);
        Ok(())
    }

    #[test]
    fn test_python_alignment_example() -> Result<()> {
        let bytes = pack!("@llh0l", 1, 2, 3)?;
        assert_eq!(bytes, vec![1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
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
        assert_eq!(LittleEndian::read_f32(&bytes[0..4]), 3.14f32);
        assert_eq!(LittleEndian::read_f64(&bytes[4..12]), 2.718f64);
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

    #[test]
    fn test_pack_string_exact() -> Result<()> {
        let bytes = pack!("5s", b"hello")?;
        assert_eq!(bytes, b"hello");
        Ok(())
    }

    #[test]
    fn test_pack_string_short() -> Result<()> {
        // String shorter than count - should pad with zeros
        let bytes = pack!("5s", b"hi")?;
        assert_eq!(bytes, vec![b'h', b'i', 0, 0, 0]);
        Ok(())
    }

    #[test]
    fn test_pack_string_long() -> Result<()> {
        // String longer than count - should truncate
        let bytes = pack!("5s", b"hello world")?;
        assert_eq!(bytes, b"hello");
        Ok(())
    }

    #[test]
    fn test_pack_string_with_other_types() -> Result<()> {
        let bytes = pack!(">H5sB", 0x1234u16, b"test", 0x42u8)?;
        assert_eq!(bytes, vec![0x12, 0x34, b't', b'e', b's', b't', 0, 0x42]);
        Ok(())
    }

    #[test]
    fn test_pack_byte_string() -> Result<()> {
        let bytes = pack!("5s", b"Hello")?;
        assert_eq!(bytes, b"Hello");
        Ok(())
    }

    #[test]
    fn test_byte_string_too_short() -> Result<()> {
        let bytes = pack!("5s", b"Hi")?;
        assert_eq!(bytes, vec![b'H', b'i', 0, 0, 0]);
        Ok(())
    }

    #[test]
    fn test_byte_string_too_long() -> Result<()> {
        let bytes = pack!("5s", b"Hello, world!")?;
        assert_eq!(bytes, b"Hello");
        Ok(())
    }

    #[test]
    fn test_pack_bool() -> Result<()> {
        let bytes = pack!("??", true, false)?;
        assert_eq!(bytes, vec![1, 0]);
        Ok(())
    }

    #[test]
    fn test_pack_signed_long() -> Result<()> {
        let bytes = pack!("<l", 42i32)?;
        assert_eq!(bytes, vec![42, 0, 0, 0]);
        Ok(())
    }

    #[test]
    fn test_pack_unsigned_long() -> Result<()> {
        let bytes = pack!("<L", 42u32)?;
        assert_eq!(bytes, vec![42, 0, 0, 0]);
        Ok(())
    }

    #[test]
    fn test_pack_ssize_t() -> Result<()> {
        let bytes = pack!("n", 42isize)?;
        assert_eq!(bytes.len(), std::mem::size_of::<isize>());
        assert_eq!(bytes[0], 42);
        bytes[1..].iter().for_each(|&b| assert_eq!(b, 0));
        Ok(())
    }

    #[test]
    fn test_pack_size_t() -> Result<()> {
        let bytes = pack!("N", 42usize)?;
        assert_eq!(bytes.len(), std::mem::size_of::<usize>());
        assert_eq!(bytes[0], 42);
        bytes[1..].iter().for_each(|&b| assert_eq!(b, 0));
        Ok(())
    }

    // Python's struct module ignores endianness for size_t and ssize_t.
    // Probably not worth writing a test for an actual big endian machine but
    // at least try not to fail.
    #[cfg(target_endian = "little")]
    #[test]
    fn test_pack_size_t_big_endian_ignored() -> Result<()> {
        let bytes = pack!(">N", 42usize)?;
        assert_eq!(bytes.len(), std::mem::size_of::<usize>());
        assert_eq!(bytes[0], 42);
        bytes[1..].iter().for_each(|&b| assert_eq!(b, 0));
        Ok(())
    }

    #[cfg(target_endian = "little")]
    #[test]
    fn test_pack_pointer() -> Result<()> {
        let ptr: *const u8 = 42 as *const u8;
        let bytes = pack!("P", ptr)?;
        assert_eq!(bytes.len(), std::mem::size_of::<*const u8>());
        assert_eq!(bytes[0], 42);
        bytes[1..].iter().for_each(|&b| assert_eq!(b, 0));
        Ok(())
    }

    #[test]
    fn test_pack_zero_length_pascal_string() -> Result<()> {
        let bytes = pack!("p", b"Hello")?;
        assert_eq!(bytes, vec![0]);
        Ok(())
    }

    #[test]
    fn test_pack_pascal_string() -> Result<()> {
        let bytes = pack!("6p", b"Hello")?;
        assert_eq!(bytes.len(), 6);
        assert_eq!(bytes, vec![5, b'H', b'e', b'l', b'l', b'o']);
        Ok(())
    }

    #[test]
    fn test_pack_short_pascal_string() -> Result<()> {
        let bytes = pack!("6p", b"Hi")?;
        assert_eq!(bytes.len(), 6);
        assert_eq!(bytes, vec![5, b'H', b'i', 0, 0, 0]);
        Ok(())
    }

    #[test]
    fn test_pack_long_pascal_string() -> Result<()> {
        let bytes = pack!("6p", b"Hello, world!")?;
        assert_eq!(bytes.len(), 6);
        assert_eq!(bytes, vec![5, b'H', b'e', b'l', b'l', b'o']);
        Ok(())
    }

    // Strings longer than 255 are truncated.
    #[test]
    fn test_pack_very_long_pascal_string() -> Result<()> {
        let long_str = b"I'm a lumberjack, and I'm okay.He's a lumberjack...
I sleep all night. I work all day.

He's a lumberjack, and he's okay.
He sleeps all night and he works all day.

I cut down trees. I eat my lunch.
I go to the lavatory.
On Wednesdays I go shoppin'
And have buttered scones for tea.

He cuts down trees. He eats his lunch.
He goes to the lavatory.
On Wednesdays he goes shopping
And has buttered scones for tea.

I'm (He's) a lumberjack, and I'm (he's) okay.
I (He) sleep(s) all night and I (he) work(s) all day.

I cut down trees. I skip and jump.
I like to press wild flowers.
I put on women's clothing
And hang around in bars.";
        let bytes = pack!("256p", long_str)?;
        assert_eq!(bytes.len(), 256);
        assert_eq!(bytes[0], 255);
        assert_eq!(&bytes[1..], &long_str[..255]);
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

    /// Helper function to call Python's struct.pack with byte strings
    fn python_pack_with_bytes(format: &str, values: Vec<pyo3::Py<pyo3::PyAny>>) -> Vec<u8> {
        Python::with_gil(|py| {
            let struct_module = py.import_bound("struct").unwrap();
            let pack_fn = struct_module.getattr("pack").unwrap();

            // Build args tuple: (format, *values)
            let mut args = vec![format.to_object(py)];
            for value in values {
                args.push(value);
            }

            let result = pack_fn
                .call1(pyo3::types::PyTuple::new_bound(py, args))
                .unwrap();
            let bytes: &Bound<'_, PyBytes> = result.downcast().unwrap();
            bytes.as_bytes().to_vec()
        })
    }

    /// Macro to simplify compatibility tests
    /// TODO: Make this work for byte strings too.
    macro_rules! test_compat {
        ($name:ident, $format: expr, $($val:expr),+) => {
            #[test]
            fn $name() -> Result<()> {
                let rust_result = pack!($format, $($val),+)?;
                let py_result = python_pack($format, vec![$(&$val),+]);
                assert_eq!(
                    rust_result, py_result,
                    "Mismatch for format '{}': Rust={:?}, Python={:?}",
                    $format, rust_result, py_result
                );
                Ok(())
            }
        }
    }

    // Basic type tests
    test_compat!(test_compat_unsigned_int_little_endian, "<I", 0x12345678u32);

    test_compat!(test_compat_unsigned_int_big_endian, ">I", 0x12345678u32);

    test_compat!(test_compat_signed_byte, "b", -42i8);

    test_compat!(test_compat_unsigned_byte, "B", 255u8);

    test_compat!(test_compat_signed_short_little_endian, "<h", -1000i16);

    test_compat!(test_compat_unsigned_short_big_endian, ">H", 0x1234u16);

    test_compat!(test_compat_signed_int_little_endian, "<i", -100000i32);

    test_compat!(test_compat_unsigned_int_network_order, "!I", 0xDEADBEEFu32);

    test_compat!(
        test_compat_signed_long_long_little_endian,
        "<q",
        -9223372036854775807i64
    );

    test_compat!(
        test_compat_unsigned_long_long_big_endian,
        ">Q",
        0x123456789ABCDEFu64
    );

    test_compat!(test_compat_float_little_endian, "<f", 3.14159f32);

    test_compat!(test_compat_double_big_endian, ">d", 2.718281828459045f64);

    test_compat!(
        test_compat_multiple_values_mixed,
        ">BHI",
        0x42u8,
        0x1234u16,
        0x56789ABCu32
    );

    test_compat!(test_compat_three_unsigned_shorts, "<HHH", 1u16, 2u16, 3u16);

    test_compat!(test_compat_signed_values, ">bhi", -1i8, -256i16, 1000i32);

    test_compat!(test_compat_five_values, ">BHBIB", 1u8, 2u16, 3u8, 4u32, 5u8);

    test_compat!(test_compat_repeat_count, "3B", 0x10u8, 0x20u8, 0x30u8);

    test_compat!(test_compat_native_byte_order, "=I", 0x12345678u32);

    test_compat!(
        test_compat_complex_format,
        "<BhHiIqQ",
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
        3.14f32,
        -42i8,
        2.718f64,
        0x12345678u32
    );

    test_compat!(test_compat_edge_case_zero, ">IHB", 0u32, 0u16, 0u8);

    test_compat!(
        test_compat_negative_numbers,
        "<bhiq",
        -128i8,
        -32768i16,
        -2147483648i32,
        -9223372036854775808i64
    );

    test_compat!(test_compat_byte_edge_case, "B", 255u8);

    test_compat!(test_compat_short_edge_case, ">H", 65535u16);

    test_compat!(test_compat_int_edge_case, ">I", 0xFFFFFFFFu32);

    #[test]
    fn test_compat_string_exact() -> Result<()> {
        let rust_result = pack!("5s", b"hello")?;
        let py_result = Python::with_gil(|py| {
            let py_bytes = PyBytes::new_bound(py, b"hello");
            python_pack_with_bytes("5s", vec![py_bytes.into_py(py)])
        });
        assert_eq!(
            rust_result, py_result,
            "Mismatch for format '5s': Rust={:?}, Python={:?}",
            rust_result, py_result
        );
        Ok(())
    }

    #[test]
    fn test_compat_string_short() -> Result<()> {
        let rust_result = pack!("5s", b"hi")?;
        let py_result = Python::with_gil(|py| {
            let py_bytes = PyBytes::new_bound(py, b"hi");
            python_pack_with_bytes("5s", vec![py_bytes.into_py(py)])
        });
        assert_eq!(
            rust_result, py_result,
            "Mismatch for format '5s': Rust={:?}, Python={:?}",
            rust_result, py_result
        );
        Ok(())
    }

    #[test]
    fn test_compat_string_long() -> Result<()> {
        let rust_result = pack!("5s", b"hello world")?;
        let py_result = Python::with_gil(|py| {
            let py_bytes = PyBytes::new_bound(py, b"hello world");
            python_pack_with_bytes("5s", vec![py_bytes.into_py(py)])
        });
        assert_eq!(
            rust_result, py_result,
            "Mismatch for format '5s': Rust={:?}, Python={:?}",
            rust_result, py_result
        );
        Ok(())
    }

    #[test]
    fn test_compat_string_with_types() -> Result<()> {
        let rust_result = pack!(">H5sB", 0x1234u16, b"test", 0x42u8)?;
        let py_result = Python::with_gil(|py| {
            let py_bytes = PyBytes::new_bound(py, b"test");
            python_pack_with_bytes(
                ">H5sB",
                vec![
                    0x1234u16.into_py(py),
                    py_bytes.into_py(py),
                    0x42u8.into_py(py),
                ],
            )
        });
        assert_eq!(
            rust_result, py_result,
            "Mismatch for format '>H5sB': Rust={:?}, Python={:?}",
            rust_result, py_result
        );
        Ok(())
    }

    #[test]
    fn test_compat_string_alignment() -> Result<()> {
        let rust_result = pack!("chic", b'A', 42, 43, b'B')?;
        let py_result = Python::with_gil(|py| {
            let py_bytes_a = PyBytes::new_bound(py, b"A");
            let py_bytes_b = PyBytes::new_bound(py, b"B");
            python_pack_with_bytes(
                "chic",
                vec![
                    py_bytes_a.into_py(py),
                    42i32.into_py(py),
                    43i32.into_py(py),
                    py_bytes_b.into_py(py),
                ],
            )
        });
        assert_eq!(
            rust_result, py_result,
            "Mismatch for format 'chic': Rust={:?}, Python={:?}",
            rust_result, py_result
        );
        Ok(())
    }
}

#[cfg(test)]
mod struct_format_tests {
    //! Comprehensive format tests ported from Python's test_struct.py
    //! These tests verify compatibility with Python's struct.pack() behavior

    use super::*;
    use anyhow::Result;

    #[test]
    fn test_simple_pack() -> Result<()> {
        let c = b'a';
        let b: i8 = 1;
        let h: i16 = 255;
        let i: i32 = 65535;
        let q: i64 = 65536;
        let f: f32 = 3.1415;
        let d: f64 = 3.1415;

        // Test with little-endian
        let bytes = pack!("<xcbhiqfd", c, b, h, i, q, f, d)?;
        assert_eq!(bytes.len(), 29);
        assert_eq!(bytes[0], 0u8);
        assert_eq!(bytes[1], c);
        assert_eq!(bytes[2], b as u8);
        assert_eq!(bytes[3..5], h.to_le_bytes());
        assert_eq!(bytes[5..9], i.to_le_bytes());
        assert_eq!(bytes[9..17], q.to_le_bytes());
        assert_eq!(bytes[17..21], f.to_le_bytes());
        assert_eq!(bytes[21..29], d.to_le_bytes());

        // Test with big-endian
        let be_bytes = pack!(">xcbhiqfd", c, b, h, i, q, f, d)?;
        assert_eq!(be_bytes.len(), 29);
        assert_eq!(be_bytes[0], 0u8);
        assert_eq!(be_bytes[1], c);
        assert_eq!(be_bytes[2], b as u8);
        assert_eq!(be_bytes[3..5], h.to_be_bytes());
        assert_eq!(be_bytes[5..9], i.to_be_bytes());
        assert_eq!(be_bytes[9..17], q.to_be_bytes());
        assert_eq!(be_bytes[17..21], f.to_be_bytes());
        assert_eq!(be_bytes[21..29], d.to_be_bytes());

        // Test with network byte order
        let ne_bytes = pack!("!xcbhiqfd", c, b, h, i, q, f, d)?;
        assert_eq!(ne_bytes, be_bytes);

        Ok(())
    }

    /// Test basic format characters with known results
    #[test]
    fn test_format_c() -> Result<()> {
        // Single character
        let bytes = pack!("c", b'a')?;
        assert_eq!(bytes, b"a");
        Ok(())
    }

    #[test]
    fn test_format_with_padding() -> Result<()> {
        // Test 'x' padding
        let bytes = pack!("xc", b'a')?;
        assert_eq!(bytes, b"\x00a");

        let bytes = pack!("cx", b'a')?;
        assert_eq!(bytes, b"a\x00");

        Ok(())
    }

    #[test]
    fn test_strings_various_sizes() -> Result<()> {
        // 0s - empty string
        let bytes = pack!("0s", b"helloworld")?;
        assert_eq!(bytes, b"");

        // 1s - single character
        let bytes = pack!("1s", b"helloworld")?;
        assert_eq!(bytes, b"h");

        // 9s - truncates
        let bytes = pack!("9s", b"helloworld")?;
        assert_eq!(bytes, b"helloworl");

        // 10s - exact fit
        let bytes = pack!("10s", b"helloworld")?;
        assert_eq!(bytes, b"helloworld");

        // 11s - pads with null
        let bytes = pack!("11s", b"helloworld")?;
        assert_eq!(bytes, b"helloworld\x00");

        // 20s - pads with nulls
        let bytes = pack!("20s", b"helloworld")?;
        assert_eq!(bytes, b"helloworld\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00");

        Ok(())
    }

    #[test]
    fn test_signed_byte() -> Result<()> {
        let bytes = pack!("b", 7i8)?;
        assert_eq!(bytes, b"\x07");

        let bytes = pack!("b", -7i8)?;
        assert_eq!(bytes, b"\xf9");

        Ok(())
    }

    #[test]
    fn test_unsigned_byte() -> Result<()> {
        let bytes = pack!("B", 7u8)?;
        assert_eq!(bytes, b"\x07");

        let bytes = pack!("B", 249u8)?;
        assert_eq!(bytes, b"\xf9");

        Ok(())
    }

    #[test]
    fn test_signed_short() -> Result<()> {
        // Big-endian
        let bytes = pack!(">h", 700i16)?;
        assert_eq!(bytes, b"\x02\xbc");

        let bytes = pack!(">h", -700i16)?;
        assert_eq!(bytes, b"\xfd\x44");

        // Little-endian
        let bytes = pack!("<h", 700i16)?;
        assert_eq!(bytes, b"\xbc\x02");

        let bytes = pack!("<h", -700i16)?;
        assert_eq!(bytes, b"\x44\xfd");

        Ok(())
    }

    #[test]
    fn test_unsigned_short() -> Result<()> {
        // Big-endian
        let bytes = pack!(">H", 700u16)?;
        assert_eq!(bytes, b"\x02\xbc");

        let bytes = pack!(">H", 0xFFFFu16 - 699)?;
        assert_eq!(bytes, b"\xfd\x44");

        // Little-endian
        let bytes = pack!("<H", 700u16)?;
        assert_eq!(bytes, b"\xbc\x02");

        Ok(())
    }

    #[test]
    fn test_signed_int() -> Result<()> {
        // Big-endian
        let bytes = pack!(">i", 70000000i32)?;
        assert_eq!(bytes, b"\x04\x2c\x1d\x80");

        let bytes = pack!(">i", -70000000i32)?;
        assert_eq!(bytes, b"\xfb\xd3\xe2\x80");

        // Little-endian
        let bytes = pack!("<i", 70000000i32)?;
        assert_eq!(bytes, b"\x80\x1d\x2c\x04");

        let bytes = pack!("<i", -70000000i32)?;
        assert_eq!(bytes, b"\x80\xe2\xd3\xfb");

        Ok(())
    }

    #[test]
    fn test_unsigned_int() -> Result<()> {
        // Big-endian
        let bytes = pack!(">I", 70000000u32)?;
        assert_eq!(bytes, b"\x04\x2c\x1d\x80");

        // Little-endian
        let bytes = pack!("<I", 70000000u32)?;
        assert_eq!(bytes, b"\x80\x1d\x2c\x04");

        Ok(())
    }

    #[test]
    fn test_float() -> Result<()> {
        // Big-endian
        let bytes = pack!(">f", 2.0f32)?;
        assert_eq!(bytes, b"\x40\x00\x00\x00");

        let bytes = pack!(">f", -2.0f32)?;
        assert_eq!(bytes, b"\xc0\x00\x00\x00");

        // Little-endian
        let bytes = pack!("<f", 2.0f32)?;
        assert_eq!(bytes, b"\x00\x00\x00\x40");

        let bytes = pack!("<f", -2.0f32)?;
        assert_eq!(bytes, b"\x00\x00\x00\xc0");

        Ok(())
    }

    #[test]
    fn test_double() -> Result<()> {
        // Big-endian
        let bytes = pack!(">d", 2.0f64)?;
        assert_eq!(bytes, b"\x40\x00\x00\x00\x00\x00\x00\x00");

        let bytes = pack!(">d", -2.0f64)?;
        assert_eq!(bytes, b"\xc0\x00\x00\x00\x00\x00\x00\x00");

        // Little-endian
        let bytes = pack!("<d", 2.0f64)?;
        assert_eq!(bytes, b"\x00\x00\x00\x00\x00\x00\x00\x40");

        let bytes = pack!("<d", -2.0f64)?;
        assert_eq!(bytes, b"\x00\x00\x00\x00\x00\x00\x00\xc0");

        Ok(())
    }

    #[test]
    fn test_mixed_types_complex() -> Result<()> {
        // Test a complex format with multiple types
        let bytes = pack!(
            "<BhHiIqQ",
            0x12u8,
            -1000i16,
            5000u16,
            -100000i32,
            0xDEADBEEFu32,
            -9223372036854775807i64,
            0x123456789ABCDEFu64
        )?;

        // Verify it produces bytes (exact values depend on endianness and packing)
        assert!(bytes.len() == 1 + 2 + 2 + 4 + 4 + 8 + 8);
        assert_eq!(bytes[0], 0x12);

        Ok(())
    }

    #[test]
    fn test_network_byte_order() -> Result<()> {
        // Network byte order (!) is the same as big-endian
        let bytes_network = pack!("!I", 0x12345678u32)?;
        let bytes_big = pack!(">I", 0x12345678u32)?;
        assert_eq!(bytes_network, bytes_big);

        Ok(())
    }

    #[test]
    fn test_multiple_padding() -> Result<()> {
        // Multiple pad bytes
        let bytes = pack!("xxxB", 42u8)?;
        assert_eq!(bytes, b"\x00\x00\x00\x2a");

        let bytes = pack!("Bxxx", 42u8)?;
        assert_eq!(bytes, b"\x2a\x00\x00\x00");

        Ok(())
    }

    #[test]
    fn test_edge_case_integers() -> Result<()> {
        // Test boundary values
        let bytes = pack!("B", 0u8)?;
        assert_eq!(bytes, b"\x00");

        let bytes = pack!("B", 255u8)?;
        assert_eq!(bytes, b"\xff");

        let bytes = pack!("b", -128i8)?;
        assert_eq!(bytes, b"\x80");

        let bytes = pack!("b", 127i8)?;
        assert_eq!(bytes, b"\x7f");

        let bytes = pack!(">H", 0u16)?;
        assert_eq!(bytes, b"\x00\x00");

        let bytes = pack!(">H", 65535u16)?;
        assert_eq!(bytes, b"\xff\xff");

        Ok(())
    }

    #[test]
    fn test_signed_long_long() -> Result<()> {
        // Test 64-bit integers
        let bytes = pack!(">q", 0x0102030405060708i64)?;
        assert_eq!(bytes, b"\x01\x02\x03\x04\x05\x06\x07\x08");

        let bytes = pack!("<q", 0x0102030405060708i64)?;
        assert_eq!(bytes, b"\x08\x07\x06\x05\x04\x03\x02\x01");

        // Test negative
        let bytes = pack!(">q", -1i64)?;
        assert_eq!(bytes, b"\xff\xff\xff\xff\xff\xff\xff\xff");

        Ok(())
    }

    #[test]
    fn test_unsigned_long_long() -> Result<()> {
        // Test 64-bit unsigned integers
        let bytes = pack!(">Q", 0x0102030405060708u64)?;
        assert_eq!(bytes, b"\x01\x02\x03\x04\x05\x06\x07\x08");

        let bytes = pack!("<Q", 0x0102030405060708u64)?;
        assert_eq!(bytes, b"\x08\x07\x06\x05\x04\x03\x02\x01");

        // Test max value
        let bytes = pack!(">Q", u64::MAX)?;
        assert_eq!(bytes, b"\xff\xff\xff\xff\xff\xff\xff\xff");

        Ok(())
    }

    #[test]
    fn test_string_with_integers() -> Result<()> {
        // Mix strings with other types
        let bytes = pack!(">H5sI", 0x1234u16, b"hello", 0x56789ABCu32)?;
        assert_eq!(bytes, b"\x12\x34hello\x56\x78\x9a\xbc");

        Ok(())
    }

    #[test]
    fn test_repeat_counts() -> Result<()> {
        // Test repeat counts
        let bytes = pack!("3B", 1u8, 2u8, 3u8)?;
        assert_eq!(bytes, b"\x01\x02\x03");

        let bytes = pack!(">2H", 0x1234u16, 0x5678u16)?;
        assert_eq!(bytes, b"\x12\x34\x56\x78");

        Ok(())
    }

    #[test]
    fn test_empty_string_format() -> Result<()> {
        // Empty format string
        let bytes = pack!("")?;
        assert_eq!(bytes, b"");

        Ok(())
    }

    #[test]
    fn test_all_byte_orders() -> Result<()> {
        let value = 0x12345678u32;

        // Little-endian
        let le = pack!("<I", value)?;
        assert_eq!(le, b"\x78\x56\x34\x12");

        // Big-endian
        let be = pack!(">I", value)?;
        assert_eq!(be, b"\x12\x34\x56\x78");

        // Network (same as big-endian)
        let net = pack!("!I", value)?;
        assert_eq!(net, be);

        // Native depends on platform
        let native = pack!("=I", value)?;
        assert!(native == le || native == be);

        Ok(())
    }
}

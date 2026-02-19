# Packadder

_A crate for packing binary structs like Python's [`struct.pack()`](https://docs.python.org/3/library/struct.html)._


## Example

```rust
use packadder::pack;
let bytes = pack!(">h", 1023)?;
assert_eq!(bytes, vec![0x03, 0xff]);
```

## Format Specifiers

### Byte Order / Alignment

The first character of the format string can specify the byte order, size, and alignment:

| Character | Byte Order | Size | Alignment | Notes |
|-----------|------------|------|-----------|-------|
| `@` | Native | Native | Native | Default. Uses C struct alignment rules |
| `=` | Native | Standard | None | Native endianness, no alignment padding |
| `<` | Little-endian | Standard | None | |
| `>` | Big-endian | Standard | None | |
| `!` | Big-endian | Standard | None | Network byte order (same as `>`) |

If no byte order character is specified, `@` is used by default.

### Format Characters

Format characters specify the data type to pack. An optional repeat count can precede the format character (e.g., `3i` for 3 integers).

| Format | C Type | Rust Type | Size (bytes) | Notes |
|--------|--------|-----------|--------------|-------|
| `x` | — | — | 1 | No value consumed |
| `c` | char | `u8` | 1 | |
| `b` | signed char | `i8` | 1 | |
| `B` | unsigned char | `u8` | 1 | |
| `?` | _Bool | `bool` | 1 | |
| `h` | short | `i16` | 2 | |
| `H` | unsigned short | `u16` | 2 | |
| `i` | int | `i32` | 4 | |
| `I` | unsigned int | `u32` | 4 | |
| `l` | long | `i32` | 4 | |
| `L` | unsigned long | `u32` | 4 | |
| `q` | long long | `i64` | 8 | |
| `Q` | unsigned long long | `u64` | 8 | |
| `n` | ssize_t | `isize` | Native | Platform-dependent size |
| `N` | size_t | `usize` | Native | Platform-dependent size |
| `f` | float | `f32` | 4 | |
| `d` | double | `f64` | 8 | |
| `s` | char[] | `&[u8]` | Variable | Fixed-length byte string. Count specifies length. Pads with zeros if input is short, truncates if long. |
| `p` | char[] | `&[u8]` | Variable | Pascal string: 1-byte length prefix followed by data. Count includes the length byte. |
| `P` | void* | `*const _` | Native | Pointer, platform-dependent size |
| `e` | — | — | 2 | ❌ Half-precision float (not yet supported) |
| `F` | — | — | 8 | ❌ Float complex (not yet supported) |
| `D` | — | — | 16 | ❌ Double complex (not yet supported) |

**Notes:**
- Standard size: Uses fixed sizes regardless of platform.
- Native size: Size depends on the platform (e.g., `n` is 4 bytes on x86 and 8 bytes on x86_64).
- With `@` alignment: Fields are aligned to their natural boundaries (e.g., `i32` aligns to 4-byte boundary).

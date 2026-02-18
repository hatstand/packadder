# Packadder

_A crate for packing binary structs like Python's `struct.pack()`._


## Example

```rust
use packadder::pack;
let bytes = pack!(">h", 1023)?;
assert_eq!(bytes, vec![0x03, 0xff]);
```
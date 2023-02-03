# A simple BCD primitive
[![CI](https://github.com/rmja/nobcd/actions/workflows/ci.yml/badge.svg)](https://github.com/rmja/nobcd/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/nobcd.svg)](https://crates.io/crates/nobcd)

This crate provides a simple `BcdNumber` type that can be used in embedded `no_std` environments.

If you are missing a feature or would like to add a new scheme, please raise an issue or a PR.

## Example
```rust
let bcd = BcdNumber::<2>::try_new(1234u16).unwrap();
assert_eq!(1234u16, bcd.value());
assert_eq!([0x12, 0x34], bcd.bcd_bytes());
assert_eq!(bcd, BcdNumber::try_from([0x12, 0x34]).unwrap());
```

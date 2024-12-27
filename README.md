[![Build](https://github.com/pascaldekloe/b10/actions/workflows/rust.yml/badge.svg)](https://github.com/pascaldekloe/b10/actions/workflows/rust.yml)

## Decimal Numbers For The Rust Programming Language

The API provides a light-weight alternative to arbitrary-precision arithmetic.
The `const` generics for base-ten exponents fix the computation steps involved
at compile time. You basically get the speed of 64-bit primitives combined with
the safety from big-number implementations.

```rust
let cents = b10::BaseCount::<-2>::from(199);
assert_eq!("€ 1.99", format!("€ {cents}"));
```

All operation is lossless by design unless explicitly stated otherwise in the
name of the respective method. The lossless guarantee applies to parsing and
formatting too. Can't read nor write digits beyond the base resolution.

```rust
// metric prefixes
use b10::{Milli, Nano, Pico};
let mA = Milli::from(100);
let ns = Nano::from(4);

// multiply into another base
let (pC, overflow):(Pico, Pico) = mA.product(ns);
if overflow != Pico::ZERO {
    panic!("product exceeds 2⁶⁴ − 1 pico");
}

// pretty formatting options
assert_eq!(
    "0.100 × 0.000000004 = 0.000000000400",
    format!("{mA} × {ns} = {pC}"),
);
assert_eq!(
    "100E-3 × 4E-9 = 400E-12",
    format!("{mA:E} × {ns:E} = {pC:E}"),
);
assert_eq!(
    "100 mA × 4 ns = 400 pC",
    format!("{mA:#}A × {ns:#}s = {pC:#}C"),
);
```

This is free and unencumbered software released into the
[public domain](https://creativecommons.org/publicdomain/zero/1.0).

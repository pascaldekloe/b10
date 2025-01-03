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

Formatting and parsing performance is on par with the Display and FromStr traits
of the standard library.

```
test fmt_tests::format_exponent_kilo       ... bench:          10.00 ns/iter (+/- 0.10)
test fmt_tests::format_exponent_u64        ... bench:           9.38 ns/iter (+/- 0.05)
test fmt_tests::format_fraction_milli      ... bench:           9.70 ns/iter (+/- 0.06)
test fmt_tests::format_fraction_u64        ... bench:          18.63 ns/iter (+/- 0.44)
test fmt_tests::format_integer_natural     ... bench:          12.40 ns/iter (+/- 4.52)
test fmt_tests::format_integer_u64         ... bench:           8.49 ns/iter (+/- 0.03)
test fmt_tests::format_sub_zero_quecto     ... bench:           8.76 ns/iter (+/- 0.06)
test fmt_tests::format_sub_zero_u64        ... bench:          22.50 ns/iter (+/- 0.14)
test text_tests::parse_bench_overhead      ... bench:           3.78 ns/iter (+/- 0.04)
test text_tests::parse_exponents_as_f64    ... bench:          29.58 ns/iter (+/- 0.27)
test text_tests::parse_exponents_as_pico   ... bench:          16.50 ns/iter (+/- 0.48)
test text_tests::parse_fractions_as_f64    ... bench:          28.10 ns/iter (+/- 0.18)
test text_tests::parse_fractions_as_nano   ... bench:          15.95 ns/iter (+/- 0.23)
test text_tests::parse_integers_as_centi   ... bench:          14.11 ns/iter (+/- 0.04)
test text_tests::parse_integers_as_natural ... bench:          13.44 ns/iter (+/- 0.10)
test text_tests::parse_integers_as_u64     ... bench:          14.22 ns/iter (+/- 0.42)
```

This is free and unencumbered software released into the
[public domain](https://creativecommons.org/publicdomain/zero/1.0).

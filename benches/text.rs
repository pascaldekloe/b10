#![feature(test)]

extern crate test;

use b10::*;

use std::io::Write;
use std::str::FromStr;
use test::bench::black_box;
use test::Bencher;

const INTEGER_TEXTS: [&str; 4] = ["1", "10", "1000", "987654321"];

/// Standard u64 parsing is the baseline.
#[bench]
fn parse_integers_as_u64(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(INTEGER_TEXTS[n % INTEGER_TEXTS.len()]);
        let got = black_box(u64::from_str(text)).unwrap();
        assert_ne!(got, 0);
    });
}

#[bench]
fn parse_integers_as_natural(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(INTEGER_TEXTS[n % INTEGER_TEXTS.len()]);
        let got = black_box(Natural::from_str(text)).unwrap();
        assert_ne!(got, Natural::ZERO);
    });
}

#[bench]
fn parse_integers_as_centi(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(INTEGER_TEXTS[n % INTEGER_TEXTS.len()]);
        let got = black_box(Centi::from_str(text)).unwrap();
        assert_ne!(got, Centi::ZERO);
    });
}

const FRACTION_TEXTS: [&str; 4] = ["1", "2003", "0.409", "987.654321"];

/// Standard f64 parsing is the baseline.
#[bench]
fn parse_fractions_as_f64(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(FRACTION_TEXTS[n % FRACTION_TEXTS.len()]);
        let got = black_box(f64::from_str(text)).unwrap();
        assert_ne!(got, 0.0);
    });
}

#[bench]
fn parse_fractions_as_nano(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(FRACTION_TEXTS[n % FRACTION_TEXTS.len()]);
        let got = black_box(Nano::from_str(text)).unwrap();
        assert_ne!(got, Nano::ZERO);
    });
}

const EXPONENT_TEXTS: [&str; 4] = ["1E0", "30E-12", "0.409E-3", "98.7654e3"];

/// Standard f64 parsing is the baseline.
#[bench]
fn parse_exponents_as_f64(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(EXPONENT_TEXTS[n % EXPONENT_TEXTS.len()]);
        let got = black_box(f64::from_str(text)).unwrap();
        assert_ne!(got, 0.0);
    });
}

#[bench]
fn parse_exponents_as_pico(b: &mut Bencher) {
    let mut n: usize = 0;
    b.iter(|| {
        n += 1;
        let text = black_box(EXPONENT_TEXTS[n % EXPONENT_TEXTS.len()]);
        let got = black_box(Pico::from_str(text)).unwrap();
        assert_ne!(got, Pico::ZERO);
    });
}

/// Standard u64 formatting is the baseline.
#[bench]
fn format_integer_u64(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let x = black_box(n);
        write!(discard, "{x}").unwrap();
    });
}

/// Speed should be similar to [format_integer_u64].
#[bench]
fn format_integer_natural(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let count = black_box(Natural::from(n));
        write!(discard, "{count}").unwrap();
    });
}

/// Standard u64 formatting is the baseline.
#[bench]
fn format_sub_zero_u64(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let x = black_box(n);
        write!(discard, "0.0000000000{x:020}").unwrap();
    });
}

/// Speed should be similar to [format_sub_zero_u64].
#[bench]
fn format_sub_zero_quecto(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let count = black_box(Quecto::from(n));
        write!(discard, "{count}").unwrap();
    });
}

/// Standard u64 formatting is the baseline.
#[bench]
fn format_fraction_u64(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        let x = black_box(n);
        let int = x / 1000;
        let frac = x % 1000;
        write!(discard, "{int}.{frac:03}").unwrap();
        n += 1;
    });
}

/// Speed should be better than [format_fraction_u64].
#[bench]
fn format_fraction_milli(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let count = black_box(Milli::from(n));
        write!(discard, "{count}").unwrap();
    });
}

/// Standard u64 formatting is the baseline.
#[bench]
fn format_exponent_u64(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let x = black_box(n);
        write!(discard, "{x}E3").unwrap();
    });
}

/// Speed should be similar to [format_exponent_u64].
#[bench]
fn format_exponent_kilo(b: &mut Bencher) {
    let mut discard = black_box(std::io::sink());
    let mut n: u64 = 0;
    b.iter(|| {
        n += 1;
        let count = black_box(Kilo::from(n));
        write!(discard, "{count:E}").unwrap();
    });
}

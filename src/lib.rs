#![feature(ascii_char)]
#![feature(ascii_char_variants)]
#![feature(bigint_helper_methods)]
#![feature(strict_overflow_ops)]

use std::ascii::Char;
use std::convert::From;
use std::fmt;

/// Count with plain integers.
pub type Natural = BaseCount<0>;

pub type Quetta = BaseCount<30>;
pub type Ronna = BaseCount<27>;
pub type Yotta = BaseCount<24>;
pub type Zetta = BaseCount<21>;
pub type Exa = BaseCount<18>;
pub type Peta = BaseCount<15>;
pub type Tera = BaseCount<12>;
pub type Giga = BaseCount<9>;
pub type Mega = BaseCount<6>;
pub type Kilo = BaseCount<3>;
pub type Hecto = BaseCount<2>;
pub type Deca = BaseCount<1>;
pub type Deci = BaseCount<-1>;
pub type Centi = BaseCount<-2>;
pub type Milli = BaseCount<-3>;
pub type Micro = BaseCount<-6>;
pub type Nano = BaseCount<-9>;
pub type Pico = BaseCount<-12>;
pub type Femto = BaseCount<-15>;
pub type Atto = BaseCount<-18>;
pub type Zepto = BaseCount<-21>;
pub type Yocto = BaseCount<-24>;
pub type Ronto = BaseCount<-27>;
pub type Quecto = BaseCount<-30>;

/// Count a base number, which is a generic exponent of ten.
/// EXP can be seen as the resolution of the count, i.e., EXP
/// 3 counts per thousand, and -2 counts with two fractions.
///
/// ```
/// let cents = b10::BaseCount::<-2>::from(199);
/// assert_eq!("€ 1.99", format!("€ {cents}"));
/// ```
#[derive(Clone, Copy, PartialEq)]
pub struct BaseCount<const EXP: i8> {
    c: u64,
}

/// Zero is the default.
impl<const EXP: i8> Default for BaseCount<EXP> {
    fn default() -> Self {
        return Self::ZERO;
    }
}

/// Count Adoption
///
/// ```
/// let degrees = b10::Deci::from(192);
/// assert_eq!("19.2 ℃", format!("{degrees} ℃"));
/// ```
impl<const EXP: i8> From<u64> for BaseCount<EXP> {
    /// Apply the count to the base component.
    fn from(count: u64) -> Self {
        return Self { c: count };
    }
}

/// Count Extraction
///
/// ```
/// type Century = b10::BaseCount::<2>;
/// let last = Century::map_n(1900).unwrap();
/// assert_eq!(19, u64::from(last));
/// ```
impl<const EXP: i8> From<BaseCount<EXP>> for u64 {
    /// Decouple the count from the base component.
    fn from(c: BaseCount<EXP>) -> u64 {
        return c.c;
    }
}

/// Numeric Values & Attributes
impl<const EXP: i8> BaseCount<EXP> {
    /// Numeric value 0 is always in range.
    pub const ZERO: Self = Self { c: 0 };

    /// The smallest numeric value in range is 10 to the power of EXP.
    pub const MIN: Self = Self { c: 1 };

    /// The largest numeric value in range is `u64::MAX` times `Self::MIN`.
    pub const MAX: Self = Self { c: u64::MAX };

    /// Get numeric value n iff an exact match within the base exponent exits,
    /// and iff the numeric value is in range `Self::MAX`.
    ///
    /// ```
    /// use b10::{Centi, Kilo};
    ///
    /// assert_eq!(Some(Centi::from(200)), Centi::map_n(2));
    /// assert_eq!(Some(Kilo::from(5)), Kilo::map_n(5000));
    ///
    /// // range protection
    /// assert_eq!(None, Centi::map_n(u64::MAX));
    /// // loss-of-precision protection
    /// assert_eq!(None, Kilo::map_n(5100));
    /// ```
    pub fn map_n(n: u64) -> Option<Self> {
        Natural::from(n).rebase()
    }

    /// Get the same numeric value under base exponent R iff an exact match
    /// exists, and iff the numeric value is in range `BaseCount<R>::MAX`.
    ///
    /// ```
    /// use b10::{Centi, Kilo};
    ///
    /// assert_eq!(Some(Centi::from(700_000)), Kilo::from(7).rebase());
    /// assert_eq!(Some(Kilo::from(7)), Centi::from(700_000).rebase());
    /// ```
    pub fn rebase<const R: i8>(self) -> Option<BaseCount<R>> {
        if const { R == EXP } {
            return Some(BaseCount::<R> { c: self.c });
        }

        if const { R < EXP } {
            let (ratio, max_in) = const {
                if R < EXP && (EXP as isize - R as isize) < 20 {
                    let ratio = 10u64.strict_pow((EXP - R) as u32);
                    (ratio, u64::MAX / ratio)
                } else {
                    // only zero can be converted
                    (0u64, 0u64)
                }
            };
            return if self.c <= max_in {
                Some(BaseCount::<R> { c: self.c * ratio })
            } else {
                // rebase overflows Self::MAX
                None
            };
        }

        assert!(const { R > EXP });

        if const { R as isize - EXP as isize > 19 } {
            // rebase underflows Self::MIN
            return None;
        }

        let downscale = const {
            // redundant check needed for compiler
            if R > EXP && (R as isize - EXP as isize) < 20 {
                10u64.strict_pow((R - EXP) as u32)
            } else {
                // not possible in this branch
                42u64 // arbitrary placeholder
            }
        };
        // modulo and division caught as one by compiler
        return if self.c % downscale == 0 {
            Some(BaseCount::<R> {
                c: self.c / downscale,
            })
        } else {
            None
        };
    }

    /// Get the SI prefix with the empty string for undefined.
    pub const fn metric_prefix() -> &'static str {
        match EXP {
            1 => "da",
            2 => "h",
            3 => "k",
            6 => "M",
            9 => "G",
            12 => "T",
            15 => "P",
            18 => "E",
            21 => "Z",
            24 => "Y",
            27 => "R",
            30 => "Q",

            -1 => "d",
            -2 => "c",
            -3 => "m",
            -6 => "µ",
            -9 => "n",
            -12 => "p",
            -15 => "f",
            -18 => "a",
            -21 => "z",
            -24 => "y",
            -27 => "r",
            -30 => "q",

            _ => "",
        }
    }
}

#[cfg(test)]
mod numeric_tests {
    use super::*;

    #[test]
    fn rebase() {
        assert_eq!(Some(Natural::from(1000)), Kilo::from(1).rebase());
        assert_eq!(Some(Kilo::from(2000)), Mega::from(2).rebase());
        assert_eq!(Some(Milli::from(3000)), Natural::from(3).rebase());
        assert_eq!(Some(Micro::from(4000)), Milli::from(4).rebase());

        // limit of 64 bits is 18_446_744_073_709_551_615
        assert_eq!(
            Some(Femto::from(18_000_000_000_000_000_000)),
            Kilo::from(18).rebase::<-15>(),
        );
        assert_eq!(None, Kilo::from(19).rebase::<-15>(),);

        // below Self::MIN
        assert_eq!(None, Exa::from(200).rebase::<0>());
        assert_eq!(None, Exa::from(300).rebase::<-128>());
        assert_eq!(None, Natural::from(400).rebase::<-18>());
        assert_eq!(None, Natural::from(500).rebase::<-128>());

        // deny rounding
        assert_eq!(None, Natural::from(123).rebase::<1>());
        assert_eq!(None, Natural::from(223).rebase::<2>());
        assert_eq!(None, Natural::from(323).rebase::<3>());
        assert_eq!(None, Natural::from(423).rebase::<4>());
    }

    /// Double check to prevent typos.
    #[test]
    fn metric_prefix() {
        assert_eq!("da", Deca::metric_prefix());
        assert_eq!("h", Hecto::metric_prefix());
        assert_eq!("k", Kilo::metric_prefix());
        assert_eq!("M", Mega::metric_prefix());
        assert_eq!("G", Giga::metric_prefix());
        assert_eq!("T", Tera::metric_prefix());
        assert_eq!("P", Peta::metric_prefix());
        assert_eq!("E", Exa::metric_prefix());
        assert_eq!("Z", Zetta::metric_prefix());
        assert_eq!("Y", Yotta::metric_prefix());
        assert_eq!("R", Ronna::metric_prefix());
        assert_eq!("Q", Quetta::metric_prefix());

        assert_eq!("d", Deci::metric_prefix());
        assert_eq!("c", Centi::metric_prefix());
        assert_eq!("m", Milli::metric_prefix());
        assert_eq!("µ", Micro::metric_prefix());
        assert_eq!("n", Nano::metric_prefix());
        assert_eq!("p", Pico::metric_prefix());
        assert_eq!("f", Femto::metric_prefix());
        assert_eq!("a", Atto::metric_prefix());
        assert_eq!("z", Zepto::metric_prefix());
        assert_eq!("y", Yocto::metric_prefix());
        assert_eq!("r", Ronto::metric_prefix());
        assert_eq!("q", Quecto::metric_prefix());
    }
}

/// Arithmetic Operation
impl<const EXP: i8> BaseCount<EXP> {
    /// Get the sum of both counts including an overflow flag. Calculation is
    /// lossless. For any pair of arguments, self + summand = sum + overflow,
    /// in which overflow represents 2 to the power of 64.
    #[inline(always)]
    pub fn sum(self, summand: Self) -> (Self, bool) {
        let (sum, overflow) = self.c.overflowing_add(summand.c);
        return (Self { c: sum }, overflow);
    }

    /// Get the product of both counts including the 64-bit overflow, if any.
    /// A compile-time check guarantees that generic P is equal to EXP + M to
    /// ensure a lossless calculation exclusively. For any pair of arguments,
    /// self × multiplicant = product + (overflow × 2^64).
    ///
    /// ```
    /// use b10::{Milli, Nano, Pico};
    ///
    /// let mA = Milli::from(100);
    /// let ns = Nano::from(4);
    /// let (pC, overflow):(Pico, Pico) = mA.product(ns);
    /// if overflow != Pico::ZERO {
    ///     panic!("too much for pico");
    /// }
    ///
    /// assert_eq!("100E-3 × 4E-9 = 400E-12",
    ///     format!("{mA:E} × {ns:E} = {pC:E}"));
    /// ```
    #[inline(always)]
    pub fn product<const M: i8, const P: i8>(
        self,
        multiplicant: BaseCount<M>,
    ) -> (BaseCount<P>, BaseCount<P>) {
        const {
            if P != EXP + M {
                panic!("generic P does not equal generic EXP plus generic M");
            }
        }
        let (product, overflow) = self.c.widening_mul(multiplicant.c);
        return (
            BaseCount::<P> { c: product },
            BaseCount::<P> { c: overflow },
        );
    }

    /// Get the quotient and the remainder for divisor, with None for division
    /// by zero. D must greater or equal to EXP. The constraint prevents numeric
    /// overflows by design.
    ///
    /// ```
    /// let price = b10::BaseCount::<-2>::from(100042);
    /// let fifty = b10::Natural::from(50);
    /// let (part, rem) = price.quotient_int(fifty).unwrap();
    ///
    /// assert_eq!("1000.42 ÷ 50 is 20 with 0.42 remaining",
    ///     format!("{price} ÷ {fifty} is {part} with {rem} remaining"));
    /// ```
    #[inline(always)]
    pub fn quotient_int<const D: i8>(self, divisor: BaseCount<D>) -> Option<(u64, Self)> {
        const {
            if D < EXP {
                // could cause numeric overflows
                panic!("divisor exponent smaller than divident exponent");
            }
        }
        if divisor.c == 0 {
            return None;
        }
        match divisor.rebase::<EXP>() {
            None => Some((0, self)), // divisor is greater than self

            Some(d) => Some((self.c / d.c, Self { c: self.c % d.c })),
        }
    }

    /// Get the quotient and the remainder for divisor constant DIV.
    ///
    /// ```
    /// let price = b10::BaseCount::<-2>::from(299);
    /// let (half, remainder) = price.quotient_const::<2>();
    ///
    /// assert_eq!("½ of 2.99 is 1.49 with 0.01 remaining",
    ///     format!("½ of {price} is {half} with {remainder} remaining"));
    /// ```
    #[inline(always)]
    pub fn quotient_const<const DIV: u64>(self) -> (Self, Self) {
        const {
            if DIV == 0 {
                panic!("zero divisor denied");
            }
        }
        return (Self { c: self.c / DIV }, Self { c: self.c % DIV });
    }
}

#[cfg(test)]
mod arithmetic_tests {
    use super::*;

    #[test]
    fn sum_overflow() {
        assert_eq!((Deci::from(6), true), Deci::MAX.sum(Deci::from(7)));
    }

    #[test]
    fn product() {
        assert_eq!(
            (Natural::from(6), Natural::ZERO),
            Natural::from(2).product(Natural::from(3))
        );
    }

    // quotient reversed with product plus remainder
    #[test]
    fn consistency() {
        let a: [u64; 7] = [0, 0, 1, 42, u64::MAX, 200, 5000];
        let b: [u64; 7] = [0, 1, 0, u64::MAX, 42, 20, 17];
        for i in 0..a.len() {
            let da = Deci::from(a[i]);
            let db = Deca::from(b[i]);

            match da.quotient_int(db) {
                None => assert_eq!(db, Deca::ZERO),
                Some((quot, rem)) => {
                    assert_ne!(db, Deca::ZERO);
                    println!("{da} ÷ {db} got {quot} with {rem} remaining");

                    let (prod, over) = Natural::from(quot).product::<1, 1>(db);
                    println!("{quot} × {db} got {prod} + {over} × 2⁶⁴");
                    assert_eq!(over, Deca::ZERO);

                    let (sum, carry) = prod.rebase::<-1>().unwrap().sum(rem);
                    println!("{prod} × {rem} got {sum} with carry {carry}");
                    assert_eq!(sum, da);
                    assert!(!carry);
                }
            };
        }
    }
}

// alias ASCII digits
const D0: Char = Char::Digit0;
const D1: Char = Char::Digit1;
const D2: Char = Char::Digit2;
const D3: Char = Char::Digit3;
const D4: Char = Char::Digit4;
const D5: Char = Char::Digit5;
const D6: Char = Char::Digit6;
const D7: Char = Char::Digit7;
const D8: Char = Char::Digit8;
const D9: Char = Char::Digit9;

// lookup table for decimal "00" up until "99"
static DOUBLE_DIGIT_TABLE: [Char; 200] = [
    D0, D0, D0, D1, D0, D2, D0, D3, D0, D4, // "00".."04"
    D0, D5, D0, D6, D0, D7, D0, D8, D0, D9, // "05".."09"
    D1, D0, D1, D1, D1, D2, D1, D3, D1, D4, // "10".."14"
    D1, D5, D1, D6, D1, D7, D1, D8, D1, D9, // "15".."19"
    D2, D0, D2, D1, D2, D2, D2, D3, D2, D4, // "20".."24"
    D2, D5, D2, D6, D2, D7, D2, D8, D2, D9, // "25".."29"
    D3, D0, D3, D1, D3, D2, D3, D3, D3, D4, // "30".."34"
    D3, D5, D3, D6, D3, D7, D3, D8, D3, D9, // "35".."39"
    D4, D0, D4, D1, D4, D2, D4, D3, D4, D4, // "40".."44"
    D4, D5, D4, D6, D4, D7, D4, D8, D4, D9, // "45".."49"
    D5, D0, D5, D1, D5, D2, D5, D3, D5, D4, // "50".."54"
    D5, D5, D5, D6, D5, D7, D5, D8, D5, D9, // "55".."59"
    D6, D0, D6, D1, D6, D2, D6, D3, D6, D4, // "60".."64"
    D6, D5, D6, D6, D6, D7, D6, D8, D6, D9, // "65".."69"
    D7, D0, D7, D1, D7, D2, D7, D3, D7, D4, // "70".."74"
    D7, D5, D7, D6, D7, D7, D7, D8, D7, D9, // "75".."79"
    D8, D0, D8, D1, D8, D2, D8, D3, D8, D4, // "80".."84"
    D8, D5, D8, D6, D8, D7, D8, D8, D8, D9, // "85".."89"
    D9, D0, D9, D1, D9, D2, D9, D3, D9, D4, // "90".."94"
    D9, D5, D9, D6, D9, D7, D9, D8, D9, D9, // "95".."99"
];

/// Textual Representation
impl<const EXP: i8> BaseCount<EXP> {
    /// Require `parse` to consume the text in full. As such, the Option always
    /// is an exact reading of the numeric value in text.
    pub fn parse_all(text: &[u8]) -> Option<Self> {
        let (c, read) = Self::parse(text);
        return if read < text.len() { None } else { Some(c) };
    }

    /// Read a numeric value from a JSON fragment until it finds either an ASCII
    /// comma (","), a closing brace ("}"), or a closing bracket ("]"). Trailing
    /// whitespace is ignored. The return is zero on error encounters.
    pub fn parse_json(fragment: &[u8]) -> (Self, usize) {
        let (c, mut i) = Self::parse(fragment);
        return loop {
            if i < fragment.len() {
                match fragment[i] {
                    // whitespace
                    b' ' | b'\t' | b'\r' | b'\n' => {
                        i += 1;
                        continue;
                    }

                    // value continuation
                    b',' | b'}' | b']' => break (c, i),

                    // error
                    _ => {}
                }
            }
            break (Self::ZERO, 0);
        };
    }

    /// Get an exact reading of the numeric value at the start of text. The
    /// `usize` in return has the number of octets parsed, which can be less
    /// than slice length. Use `parse_all` to ensure a full reading instead.
    /// Parsing is robust against malicious input. No assumptions are made on
    /// the content of text.
    ///
    /// ASCII character "." (0x2E) is recognised as a decimal separator. ASCII
    /// character "E" (0x45) and "e" (0x65) are both accepted for E notation.
    /// Non-significant digits (a.k.a. leading zeroes) are ignored/permitted.
    /// The following cases get rejected with a zero usize.
    ///
    ///  * No input: empty text slice
    ///  * Range exhaustion: any numeric value over Self::MAX
    ///  * Beyond resolution: significant digits under Self::MIN
    ///
    ///
    /// ```
    /// let label = b"1.44 MB";
    /// // micro resolution of mega value to count bytes
    /// let (read_v, read_n) = b10::Micro::parse(label);
    /// // verify parse together with unit expectation
    /// assert_eq!(b" MB", &label[read_n..]);
    /// assert_eq!(b10::Micro::from(1_440_000), read_v);
    ///
    /// // need E notation for EXP greater than zero
    /// assert_eq!((b10::Kilo::from(500), 5), b10::Kilo::parse(b"5.0E5"));
    /// // … because digits beyond the resolution are denied, even when zero
    /// assert_eq!((b10::Kilo::ZERO, 0), b10::Kilo::parse(b"1000"));
    /// assert_eq!((b10::Centi::ZERO, 0), b10::Centi::parse(b"0.500"));
    /// ```
    pub fn parse(text: &[u8]) -> (Self, usize) {
        // read number with optional E notation
        let (int, exp, parse_len) = Self::parse_as_int_exp(text);
        if parse_len == 0 {
            return (Self::ZERO, 0);
        }

        // rebase int/exp to generic EXP
        let count: Option<u64> = match exp - const { EXP as isize } {
            0 => Some(int),
            1 => int.checked_mul(10),
            2 => int.checked_mul(100),
            3 => int.checked_mul(1000),
            4 => int.checked_mul(10000),
            5 => int.checked_mul(100000),
            6 => int.checked_mul(1000000),
            7 => int.checked_mul(10000000),
            8 => int.checked_mul(100000000),
            9 => int.checked_mul(1000000000),
            10 => int.checked_mul(10000000000),
            11 => int.checked_mul(100000000000),
            12 => int.checked_mul(1000000000000),
            13 => int.checked_mul(10000000000000),
            14 => int.checked_mul(100000000000000),
            15 => int.checked_mul(1000000000000000),
            16 => int.checked_mul(10000000000000000),
            17 => int.checked_mul(100000000000000000),
            18 => int.checked_mul(1000000000000000000),
            19 => int.checked_mul(10000000000000000000),

            // beyond resolution is not permitted
            ..0 => None,

            // only non-significant digits permitted
            20.. => {
                if int == 0 {
                    Some(0)
                } else {
                    None
                }
            }
        };

        match count {
            None => (Self::ZERO, 0),
            Some(n) => (Self { c: n }, parse_len),
        }
    }

    /// Parse the number as an integer with a base-10 exponent. The usize in
    /// return has the number of octets parsed from text with zero for none.
    fn parse_as_int_exp(text: &[u8]) -> (u64, isize, usize) {
        // parsed decimals
        let mut num: u64 = 0;
        // index of first decimal (with zero for none)
        let mut fraction_offset: usize = 0;

        // read index in text
        let mut i: usize = 0;
        while i < text.len() {
            let c = text[i];

            match c {
                // decimal separator
                b'.' => {
                    if fraction_offset != 0 {
                        // two separators
                        return (0, 0, 0);
                    }
                    fraction_offset = i + 1;
                }

                b'0'..=b'9' => {
                    let digit = c as u64 - b'0' as u64;
                    if num >= u64::MAX / 10 && (num > u64::MAX / 10 || digit > 5) {
                        // numeric overflow
                        return (0, 0, 0);
                    }
                    num = num * 10 + digit;
                }

                _ => break,
            }

            i += 1;
        }

        // exponent caused by fraction is negative, if any
        let frac_exp: isize = if fraction_offset == 0 {
            0 // without fraction
        } else {
            fraction_offset as isize - i as isize
        };

        // maybe E notation
        if i >= text.len() || (text[i] != b'E' && text[i] != b'e') {
            // no E notation
            return (num, frac_exp, i);
        }
        i += 1;

        // maybe exponent sign
        let mut exp_neg = false;
        if i < text.len() && text[i] == b'-' {
            exp_neg = true;
            i += 1;
        } else if i < text.len() && text[i] == b'+' {
            // redudant sign permitted
            i += 1;
        }

        // read exponent number
        let mut exp_num: usize = 0;
        while i < text.len() && text[i] >= b'0' && text[i] <= b'9' {
            let digit = text[i] as usize - b'0' as usize;
            i += 1;

            exp_num = exp_num * 10 + digit;
            if exp_num > 0xFFFF {
                return (0, 0, 0);
            }
        }

        let exp = if exp_neg {
            frac_exp - exp_num as isize
        } else {
            frac_exp + exp_num as isize
        };
        (num, exp, i)
    }

    /// Format the integer value as ASCII with leading zeroes.
    /// The usize return counts the number of leading zeroes.
    /// Self::ZERO needs separate handling without count_digits.
    fn count_digits(&self) -> ([Char; 20], usize) {
        debug_assert_ne!(self.c, 0);

        // initialize result as "00000000000000000000"
        let mut buf: [Char; 20] = [Char::Digit0; 20];
        // leading zero count equals write index
        let mut i = buf.len();

        // format backwards; least significant first
        let mut remain = self.c;

        // print per two digits
        while remain > 9 {
            let p = (remain % 100) as usize * 2;
            remain /= 100;

            i -= 2;
            buf[i + 0] = DOUBLE_DIGIT_TABLE[p + 0];
            buf[i + 1] = DOUBLE_DIGIT_TABLE[p + 1];
        }

        // print remainder digit, if any
        if remain != 0 {
            assert!(remain < 10);
            let p = (remain as usize * 2) + 1;
            // remain = 0; // redundant

            i -= 1;
            buf[i] = DOUBLE_DIGIT_TABLE[p];
        }

        return (buf, i);
    }

    fn fmt_metric_prefix(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (suffix, frac_n): (&str, usize) = match const { EXP } {
            31.. => return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f),
            30 => (" Q", 0),
            29 => (" Q", 1),
            28 => (" Q", 2),
            27 => (" R", 0),
            26 => (" R", 1),
            25 => (" R", 2),
            24 => (" Y", 0),
            23 => (" Y", 1),
            22 => (" Y", 2),
            21 => (" Z", 0),
            20 => (" Z", 1),
            19 => (" Z", 2),
            18 => (" E", 0),
            17 => (" E", 1),
            16 => (" E", 2),
            15 => (" P", 0),
            14 => (" P", 1),
            13 => (" P", 2),
            12 => (" T", 0),
            11 => (" T", 1),
            10 => (" T", 2),
            9 => (" G", 0),
            8 => (" G", 1),
            7 => (" G", 2),
            6 => (" M", 0),
            5 => (" M", 1),
            4 => (" M", 2),
            3 => (" k", 0),
            2 => (" h", 0),
            1 => (" da", 0),
            0 => ("", 0),
            -1 => (" d", 0),
            -2 => (" c", 0),
            -3 => (" m", 0),
            -4 => (" m", 1),
            -5 => (" m", 2),
            -6 => (" µ", 0),
            -7 => (" µ", 1),
            -8 => (" µ", 2),
            -9 => (" n", 0),
            -10 => (" n", 1),
            -11 => (" n", 2),
            -12 => (" p", 0),
            -13 => (" p", 1),
            -14 => (" p", 2),
            -15 => (" f", 0),
            -16 => (" f", 1),
            -17 => (" f", 2),
            -18 => (" a", 0),
            -19 => (" a", 1),
            -20 => (" a", 2),
            -21 => (" z", 0),
            -22 => (" z", 1),
            -23 => (" z", 2),
            -24 => (" y", 0),
            -25 => (" y", 1),
            -26 => (" y", 2),
            -27 => (" r", 0),
            -28 => (" r", 1),
            -29 => (" r", 2),
            -30 => (" q", 0),
            -31 => (" q", 1),
            -32 => (" q", 2),
            ..-32 => {
                panic!("TODO: write as fraction");
            }
        };

        let (mut buf, lzc) = self.count_digits();
        match frac_n {
            0 => f.write_str(buf[lzc..].as_str())?,

            1 => {
                // last digit as fraction
                if lzc > 18 {
                    buf[18] = Char::FullStop;
                    f.write_str(buf[17..].as_str())?;
                } else {
                    f.write_str(buf[lzc..19].as_str())?;
                    buf[18] = Char::FullStop;
                    f.write_str(buf[18..].as_str())?;
                }
            }

            2 => {
                // last two digits as fraction
                if lzc > 17 {
                    buf[17] = Char::FullStop;
                    f.write_str(buf[16..].as_str())?;
                } else {
                    f.write_str(buf[lzc..18].as_str())?;
                    buf[17] = Char::FullStop;
                    f.write_str(buf[17..].as_str())?;
                }
            }

            _ => unreachable!(),
        }

        f.write_str(suffix)
    }
}

#[cfg(test)]
mod text_tests {
    use super::*;

    #[test]
    fn omission() {
        assert_eq!((0.into(), 0), Milli::parse(b""), "no text");
        assert_eq!((900.into(), 2), Milli::parse(b".9"), "no integer");
        assert_eq!((9000.into(), 2), Milli::parse(b"9."), "no fraction");
        assert_eq!((9000.into(), 2), Milli::parse(b"9E"), "no exponent");
        assert_eq!((0.into(), 2), Milli::parse(b".E"), "no nothing");
    }

    #[test]
    fn one_million() {
        let text = b"1000000";

        assert_eq!((10u64.pow(6).into(), 7), BaseCount::<0>::parse(text));

        // fractional base
        assert_eq!((10u64.pow(7).into(), 7), BaseCount::<-1>::parse(text));
        assert_eq!((10u64.pow(8).into(), 7), BaseCount::<-2>::parse(text));
        // …
        assert_eq!((10u64.pow(18).into(), 7), BaseCount::<-12>::parse(text));
        assert_eq!((10u64.pow(19).into(), 7), BaseCount::<-13>::parse(text));

        // exceed BaseCount::MAX with too many fractions
        assert_eq!((0.into(), 0), BaseCount::<-14>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<-15>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<-99>::parse(text));

        // significant digits beyond resolution
        assert_eq!((0.into(), 0), BaseCount::<1>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<2>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<3>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<4>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<5>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<6>::parse(text));
        // most-significant decimal exceeded
        assert_eq!((0.into(), 0), BaseCount::<7>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<8>::parse(text));
        assert_eq!((0.into(), 0), BaseCount::<99>::parse(text));
    }

    #[test]
    fn e_notation() {
        const E17: u64 = 10u64.pow(17);

        // exact match
        assert_eq!((42.into(), 4), BaseCount::<0>::parse(b"42E0"));
        assert_eq!((42.into(), 5), BaseCount::<0>::parse(b"42E+0"));
        assert_eq!((42.into(), 5), BaseCount::<0>::parse(b"42E-0"));
        // above base
        assert_eq!((420.into(), 5), BaseCount::<0>::parse(b"42E01"));
        assert_eq!(((42 * E17).into(), 5), BaseCount::<0>::parse(b"42E17"));

        // below base
        assert_eq!((0.into(), 0), BaseCount::<0>::parse(b"42E-1"));
        // numeric overflow
        assert_eq!((0.into(), 0), BaseCount::<0>::parse(b"42E18"));

        // high exponent
        assert_eq!((42.into(), 5), BaseCount::<60>::parse(b"42E60"));
        assert_eq!((42.into(), 6), BaseCount::<60>::parse(b"42E+60"));
        assert_eq!((420.into(), 5), BaseCount::<60>::parse(b"42E61"));
        assert_eq!(((42 * E17).into(), 5), BaseCount::<60>::parse(b"42E77"));
        assert_eq!((0.into(), 0), BaseCount::<60>::parse(b"42E59"));
        assert_eq!((0.into(), 0), BaseCount::<60>::parse(b"42E78"));

        // low exponent
        assert_eq!((42.into(), 6), BaseCount::<-60>::parse(b"42E-60"));
        assert_eq!((420.into(), 6), BaseCount::<-60>::parse(b"42E-59"));
        assert_eq!(((42 * E17).into(), 6), BaseCount::<-60>::parse(b"42E-43"));
        assert_eq!((0.into(), 0), BaseCount::<-60>::parse(b"42E-61"));
        assert_eq!((0.into(), 0), BaseCount::<-60>::parse(b"42E-42"));
    }

    #[test]
    fn max() {
        let b0 = b"18446744073709551615";
        assert_eq!((u64::MAX.into(), b0.len()), BaseCount::<0>::parse(b0));
        let b0l21 = b"00000000000000000000018446744073709551615";
        assert_eq!((u64::MAX.into(), b0l21.len()), BaseCount::<0>::parse(b0l21));

        let f1 = b"1844674407370955161.5";
        assert_eq!((u64::MAX.into(), f1.len()), BaseCount::<-1>::parse(f1));
        // …
        let f19 = b"1.8446744073709551615";
        assert_eq!((u64::MAX.into(), f19.len()), BaseCount::<-19>::parse(f19));
        let f20 = b"0.18446744073709551615";
        assert_eq!((u64::MAX.into(), f20.len()), BaseCount::<-20>::parse(f20));
        let f21 = b"0.018446744073709551615";
        assert_eq!((u64::MAX.into(), f21.len()), BaseCount::<-21>::parse(f21));
        // …
        let f39 = b"0.000000000000000000018446744073709551615";
        assert_eq!((u64::MAX.into(), f39.len()), BaseCount::<-39>::parse(f39));
        let f40 = b"0.0000000000000000000018446744073709551615";
        assert_eq!((u64::MAX.into(), f40.len()), BaseCount::<-40>::parse(f40));
        let f41 = b"0.00000000000000000000018446744073709551615";
        assert_eq!((u64::MAX.into(), f41.len()), BaseCount::<-41>::parse(f41));

        let b0e1 = b"18446744073709551615e1";
        assert_eq!((u64::MAX.into(), b0e1.len()), BaseCount::<1>::parse(b0e1));
        let f1e2 = b"1844674407370955161.5e2";
        assert_eq!((u64::MAX.into(), f1e2.len()), BaseCount::<1>::parse(f1e2));
        let f2e1 = b"184467440737095516.15e1";
        assert_eq!((u64::MAX.into(), f2e1.len()), BaseCount::<-1>::parse(f2e1));
        let f41e22n = b"0.00000000000000000000018446744073709551615e-22";
        assert_eq!(
            (u64::MAX.into(), f41e22n.len()),
            BaseCount::<-63>::parse(f41e22n)
        );
        let f41e120 = b"0.00000000000000000000018446744073709551615e120";
        assert_eq!(
            (u64::MAX.into(), f41e120.len()),
            BaseCount::<79>::parse(f41e120)
        );
    }

    #[test]
    fn parse_zero() {
        let in_nano_range = [
            "", "0", "00", "0.0", "00.0", "0.00", "00e00", "0.00e0", "00.00e-7",
        ];

        for s in in_nano_range {
            let got = Nano::parse(s.as_bytes());
            let want = (Nano::ZERO, s.len());
            assert_eq!(want, got, "parse({})", s);
        }

        // 21 non-significant digits
        let ke3 = Kilo::parse(b"000000000000000000000e3");
        assert_eq!((Kilo::ZERO, 21 + 2), ke3);
        let ke4 = Kilo::parse(b"000000000000000000000e4");
        assert_eq!((Kilo::ZERO, 21 + 2), ke4);
        assert_eq!((Milli::ZERO, 21), Milli::parse(b"000000000000000000000"));
        let ne9 = Nano::parse(b"000000000000000000000e-9");
        assert_eq!((Nano::ZERO, 21 + 3), ne9);
        let ne8 = Nano::parse(b"000000000000000000000e-8");
        assert_eq!((Nano::ZERO, 21 + 3), ne8);

        // non-significant digits far out of range
        let hi_res = BaseCount::<-128>::ZERO;
        assert_eq!((hi_res, 3), BaseCount::parse(b"0.0"));
        assert_eq!((hi_res, 5), BaseCount::parse(b"00.00"));
        assert_eq!((hi_res, 23), BaseCount::parse(b"000000000000000000000.0"));
        assert_eq!((hi_res, 23), BaseCount::parse(b"0.000000000000000000000"));
    }

    #[test]
    fn trailing_zeroes() {
        // deny trailing zeroes beyond resolution
        assert_eq!((0.into(), 0), BaseCount::<1>::parse(b"700"));
        assert_eq!((0.into(), 0), BaseCount::<2>::parse(b"700"));
        assert_eq!((0.into(), 0), BaseCount::<2>::parse(b"70E1"));
        assert_eq!((0.into(), 0), BaseCount::<0>::parse(b"7.0"));
        assert_eq!((0.into(), 0), BaseCount::<0>::parse(b"7.0E0"));
        assert_eq!((0.into(), 0), BaseCount::<0>::parse(b"7.00E1"));

        // just within range
        assert_eq!((70.into(), 5), BaseCount::<0>::parse(b"7.0E1"));
        assert_eq!((70.into(), 5), BaseCount::<1>::parse(b"7.0E2"));
        assert_eq!((70.into(), 6), BaseCount::<0>::parse(b"0.70E2"));
        assert_eq!((70.into(), 6), BaseCount::<-1>::parse(b"7.0E-0"));
    }

    // Verify the DOUBLE_DIGIT_TABLE content in full.
    #[test]
    fn count_digits() {
        // don't care about special case 0 as it is not used
        for i in 1..102 {
            let (buf, lzc) = Natural::from(i).count_digits();

            let text = buf[..].as_str();
            match text.parse::<u64>() {
                Err(e) => assert!(false, "got {} for {}: {}", text, i, e),
                Ok(v) => assert_eq!(v, i, "got {} for {}", text, i),
            };

            let dec_n: usize = i.ilog10() as usize + 1;
            let want_lzc = buf.len() - dec_n;
            assert_eq!(lzc, want_lzc, "leading-zero count for {}", text);
        }

        let (buf_max, lzc_max) = Natural::from(u64::MAX).count_digits();
        assert_eq!("18446744073709551615", buf_max.as_str());
        assert_eq!(0, lzc_max);

        let (buf_tz, lzc_tz) = Natural::from(1_000_000_000_000_000_000).count_digits();
        assert_eq!("01000000000000000000", buf_tz.as_str());
        assert_eq!(1, lzc_tz);
    }
}

/// Display the number in plain-decimal notation. Any EXP above zero causes E
/// notation instead.
///
/// Alternate formatting (with the "#" flag) displays the count of non-zero EXP
/// with a metric prefix and non-breaking space in between. EXP without prefix
/// definition get the count as a fraction of the next prefix in line, if any.
/// Otherwise, formatting falls back to E notation for any EXP above 30.
///
/// ```
/// assert_eq!("0.72 n", format!("{:#}",
///     b10::BaseCount::<-11>::from(72)));
/// assert_eq!("12345.6 G", format!("{:#}",
///     b10::BaseCount::<8>::from(123456)));
/// ```
impl<const EXP: i8> fmt::Display for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if const { EXP != 0 } && f.alternate() {
            return self.fmt_metric_prefix(f);
        }

        if const { EXP > 0 } {
            return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f);
        }

        if self.c == 0 {
            return f.write_str("0");
        }
        let (buf, lzc) = self.count_digits();

        fn write_n_zeroes(f: &mut fmt::Formatter<'_>, mut n: usize) -> fmt::Result {
            static ZEROES: [Char; 32] = [Char::Digit0; 32];
            while n > ZEROES.len() {
                f.write_str(ZEROES.as_str())?;
                n -= ZEROES.len();
            }
            if n != 0 {
                f.write_str(ZEROES[..n].as_str())?;
            }
            Ok(())
        }

        match EXP {
            0 => f.write_str(buf[lzc..].as_str()),
            1.. => {
                f.write_str(buf[lzc..].as_str())?;
                write_n_zeroes(f, EXP as usize)
            }
            -20 => {
                f.write_str("0.")?;
                f.write_str(buf.as_str())
            }
            ..-20 => {
                f.write_str("0.")?;
                write_n_zeroes(f, (-20 - EXP) as usize)?;
                f.write_str(buf.as_str())
            }
            -19..0 => {
                let dec_sep = const { EXP + 20 } as usize;
                if lzc < dec_sep {
                    f.write_str(buf[lzc..dec_sep].as_str())?;
                    f.write_str(".")?;
                } else {
                    f.write_str("0.")?;
                }
                f.write_str(buf[dec_sep..].as_str())
            }
        }
    }
}

#[cfg(test)]
mod display_tests {
    use super::*;

    #[test]
    #[rustfmt::skip]
    fn least_significant_digit() {
        assert_eq!("1", format!("{}", BaseCount::<0>::from(1)));

        assert_eq!("2E1", format!("{}", BaseCount::<1>::from(2)));
        assert_eq!("3E2", format!("{}", BaseCount::<2>::from(3)));
        assert_eq!("7E19", format!("{}", BaseCount::<19>::from(7)));
        assert_eq!("8E20", format!("{}", BaseCount::<20>::from(8)));
        assert_eq!("9E21", format!("{}", BaseCount::<21>::from(9)));

        assert_eq!("0.2", format!("{}", BaseCount::<-1>::from(2)));
        assert_eq!("0.03", format!("{}", BaseCount::<-2>::from(3)));
        assert_eq!("0.0000000000000000007", format!("{}", BaseCount::<-19>::from(7)));
        assert_eq!("0.00000000000000000008", format!("{}", BaseCount::<-20>::from(8)));
        assert_eq!("0.000000000000000000009", format!("{}", BaseCount::<-21>::from(9)));
    }

    #[test]
    #[rustfmt::skip]
    fn decimal_slide() {
        // 20 digits with leading zero
        let n = 12345678901234567890;
        assert_eq!("12345678901234567890E2", format!("{}", BaseCount::<2>::from(n)));
        assert_eq!("12345678901234567890E1", format!("{}", BaseCount::<1>::from(n)));
        assert_eq!("12345678901234567890", format!("{}", BaseCount::<0>::from(n)));
        assert_eq!("1234567890123456789.0", format!("{}", BaseCount::<-1>::from(n)));
        assert_eq!("123456789012345678.90", format!("{}", BaseCount::<-2>::from(n)));
        assert_eq!("12345678901234567.890", format!("{}", BaseCount::<-3>::from(n)));
        assert_eq!("1234567890123456.7890", format!("{}", BaseCount::<-4>::from(n)));
        assert_eq!("123456789012345.67890", format!("{}", BaseCount::<-5>::from(n)));
        assert_eq!("12345678901234.567890", format!("{}", BaseCount::<-6>::from(n)));
        assert_eq!("1234567890123.4567890", format!("{}", BaseCount::<-7>::from(n)));
        assert_eq!("123456789012.34567890", format!("{}", BaseCount::<-8>::from(n)));
        assert_eq!("12345678901.234567890", format!("{}", BaseCount::<-9>::from(n)));
        assert_eq!("1234567890.1234567890", format!("{}", BaseCount::<-10>::from(n)));
        assert_eq!("123456789.01234567890", format!("{}", BaseCount::<-11>::from(n)));
        assert_eq!("12345678.901234567890", format!("{}", BaseCount::<-12>::from(n)));
        assert_eq!("1234567.8901234567890", format!("{}", BaseCount::<-13>::from(n)));
        assert_eq!("123456.78901234567890", format!("{}", BaseCount::<-14>::from(n)));
        assert_eq!("12345.678901234567890", format!("{}", BaseCount::<-15>::from(n)));
        assert_eq!("1234.5678901234567890", format!("{}", BaseCount::<-16>::from(n)));
        assert_eq!("123.45678901234567890", format!("{}", BaseCount::<-17>::from(n)));
        assert_eq!("12.345678901234567890", format!("{}", BaseCount::<-18>::from(n)));
        assert_eq!("1.2345678901234567890", format!("{}", BaseCount::<-19>::from(n)));
        assert_eq!("0.12345678901234567890", format!("{}", BaseCount::<-20>::from(n)));
        assert_eq!("0.012345678901234567890", format!("{}", BaseCount::<-21>::from(n)));
    }
}

/// Print as `UpperExp`.
impl<const EXP: i8> fmt::Debug for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f);
    }
}

/// Print the integer count with the base [fixed].
impl<const EXP: i8> fmt::LowerExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <u64 as fmt::Display>::fmt(&self.c, f)?;
        write!(f, "e{EXP}")
    }
}

/// Print the integer count with the base [fixed].
impl<const EXP: i8> fmt::UpperExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <u64 as fmt::Display>::fmt(&self.c, f)?;
        write!(f, "E{EXP}")
    }
}

#[cfg(test)]
mod fmt_tests {
    use super::*;

    #[test]
    fn alternate() {
        assert_eq!("42", format!("{:#}", BaseCount::<0>::from(42)));
        assert_eq!("42 da", format!("{:#}", BaseCount::<1>::from(42)));
        assert_eq!("42 h", format!("{:#}", BaseCount::<2>::from(42)));
        assert_eq!("42 k", format!("{:#}", BaseCount::<3>::from(42)));
        assert_eq!("0.42 M", format!("{:#}", BaseCount::<4>::from(42)));
        assert_eq!("4.2 M", format!("{:#}", BaseCount::<5>::from(42)));
        assert_eq!("42 M", format!("{:#}", BaseCount::<6>::from(42)));
        assert_eq!("0.42 G", format!("{:#}", BaseCount::<7>::from(42)));
        // …
        assert_eq!("0.42 Q", format!("{:#}", BaseCount::<28>::from(42)));
        assert_eq!("4.2 Q", format!("{:#}", BaseCount::<29>::from(42)));
        assert_eq!("42 Q", format!("{:#}", BaseCount::<30>::from(42)));
        assert_eq!("42E31", format!("{:#}", BaseCount::<31>::from(42)));
        assert_eq!("42E32", format!("{:#}", BaseCount::<32>::from(42)));
        assert_eq!("42E33", format!("{:#}", BaseCount::<33>::from(42)));

        assert_eq!("42 d", format!("{:#}", BaseCount::<-1>::from(42)));
        assert_eq!("42 c", format!("{:#}", BaseCount::<-2>::from(42)));
        assert_eq!("42 m", format!("{:#}", BaseCount::<-3>::from(42)));
        assert_eq!("4.2 m", format!("{:#}", BaseCount::<-4>::from(42)));
        assert_eq!("0.42 m", format!("{:#}", BaseCount::<-5>::from(42)));
        assert_eq!("42 µ", format!("{:#}", BaseCount::<-6>::from(42)));
        assert_eq!("4.2 µ", format!("{:#}", BaseCount::<-7>::from(42)));
        // …
        assert_eq!("4.2 r", format!("{:#}", BaseCount::<-28>::from(42)));
        assert_eq!("0.42 r", format!("{:#}", BaseCount::<-29>::from(42)));
        assert_eq!("42 q", format!("{:#}", BaseCount::<-30>::from(42)));
        assert_eq!("4.2 q", format!("{:#}", BaseCount::<-31>::from(42)));
        assert_eq!("0.42 q", format!("{:#}", BaseCount::<-32>::from(42)));

        // TODO:
        // assert_eq!("0.042", format!("{:#}", BaseCount::<-33>::from(42)));
        // assert_eq!("0.00042", format!("{:#}", BaseCount::<-35>::from(42)));
        // …
        // assert_eq!("0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042", format!("{:#}", BaseCount::<-128>::from(42)));
    }

    #[test]
    fn exp() {
        let x = Milli::from(42);
        assert_eq!("42E-3", format!("{x:E}"), "upper case");
        assert_eq!("42e-3", format!("{x:e}"), "lower case");
        assert_eq!("42E-3", format!("{x:?}"), "as debug");

        assert_eq!("+42E-3", format!("{x:+E}"), "tolerate +");
        assert_eq!("42e-3", format!("{x:-e}"), "tolerate -");

        assert_eq!("0042E-3", format!("{x:04E}"), "zero pad");
        assert_eq!("42e-3", format!("{x:01e}"), "under pad");

        assert_eq!("42 E-3", format!("{x:<3E}"), "space fill");
    }
}

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

    /// Get the numeric value if, and only if an exact match with
    /// the base exponent exists, and if, and only if the value is
    /// in range `Self::MAX`.
    ///
    /// ```
    /// use b10::{Centi, Kilo};
    /// assert_eq!(Some(Centi::from(200)), Centi::map_n(2));
    /// assert_eq!(Some(Kilo::from(5)), Kilo::map_n(5000));
    ///
    /// // overflow protection
    /// assert_eq!(None, Centi::map_n(u64::MAX));
    /// // underflow protection
    /// assert_eq!(None, Kilo::map_n(5100));
    /// ```
    pub fn map_n(n: u64) -> Option<Self> {
        Natural::from(n).rebase()
    }

    /// Get the same numeric value under base exponent R if, and only
    /// if an exact match exists, and if, and only if the value is in
    /// range `BaseCount::<R>::MAX`.
    ///
    /// ```
    /// use b10::{Centi, Kilo};
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

// lookup table for decimal "00" up until "99".
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
    /// Require `parse` to consume the text in full.
    pub fn parse_all(text: &[u8]) -> Option<Self> {
        let (c, read) = Self::parse(text);
        return if read < text.len() { None } else { Some(c) };
    }

    /// Read a numeric value from a JSON fragment until it finds either a
    /// `,`, a `}` or a `]`. Trailing whitespace is ignored. The return is
    /// zero on error encounters.
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

    /// Get an exact reading of the numeric value in text with the dot character
    /// ('.') as a decimal separator, if any. Parsing may stop before the end of
    /// text. It is the caller's responsibility to verify the read count against
    /// expectations.
    ///
    /// The number of octets read in return (as `usize`) is zero on error, which
    /// includes any form of precission loss, like rounding or range exhaustion.
    ///
    /// ```
    /// # use std::io::Read;
    /// let label = b"1.44 MB";
    /// let (value, size) = b10::Centi::parse(label);
    /// if size >= label.len() || label[size] != b' ' {
    ///     panic!("read {size} bytes of label");
    /// }
    /// assert_eq!(b10::Centi::from(144), value);
    /// assert_eq!(b" MB", &label[size..]);
    ///
    /// // Fewer digits than the actual resultion is permitted.
    /// assert_eq!((50.into(), 3), b10::Centi::parse(b"0.5"));
    /// // stop reading beyond the resultion
    /// assert_eq!((50.into(), 4), b10::Centi::parse(b"0.500"));
    ///
    /// // The trailing zeroes exactly match one kilo.
    /// assert_eq!((1.into(), 4), b10::Kilo::parse(b"1000"));
    /// // Values outside the base resolution get rejected.
    /// assert_eq!((0.into(), 0), b10::Kilo::parse(b"1024"));
    /// ```
    ///
    /// Parse is robust against malicious input. No assumptions are made on the
    /// byte content of text. The reading stops after 20 signifcant digits.
    pub fn parse(text: &[u8]) -> (Self, usize) {
        // check leading zero with more to come
        if text.len() > 1 && text[0] == b'0' {
            return match text[1] {
                // deny redundant zeroes
                b'0'..=b'9' => (Self::ZERO, 0),

                // decimal separator
                b'.' => Self::at_fraction(text, 2, 0),

                b'e' | b'E' => Self::ZERO.at_exponent(text, 2),

                // allow plain zero regardless of base exponent
                _ => (Self::ZERO, 1),
            };
        }

        // read index in text
        let mut i: usize = 0;

        // read integer digits into v
        let mut v: u64 = 0;
        return loop {
            if i < text.len() {
                match text[i] {
                    b'0'..=b'9' => {
                        let decimal = decimal_of(text[i]);

                        // limit of 64 bits is 18_446_744_073_709_551_615
                        if i > 19 {
                            if decimal > 5 || v > u64::MAX / 10 {
                                // numeric overflow
                                break (Self::ZERO, 0);
                            }

                            // can apply the 20th digit safely now
                            assert_eq!(19, i);
                        }

                        v = (v * 10) + decimal;

                        // 🔁 next character
                        i += 1;
                        continue;
                    }

                    b'.' => break Self::at_fraction(text, i + 1, v),

                    b'e' | b'E' => break Self { c: v }.at_exponent(text, i + 1),

                    // stop parsing
                    _ => {}
                }
            }

            break match Self::map_n(v) {
                Some(c) => (c, i),
                None => (Self::ZERO, 0),
            };
        };
    }

    /// Check for an exact match with the base number.
    /// TODO: Should less precise bases be permitted?
    fn at_exponent(self, text: &[u8], mut i: usize) -> (Self, usize) {
        if EXP < 0 {
            if i >= text.len() || text[i] != b'-' {
                return (Self::ZERO, 0);
            }
            i += 1;
        }
        // TODO: Should we tolerate redundant '+' in exponent?
        // TODO: How about "E-0" and "E+0"?

        let same_as_base = if const { EXP > -10 && EXP < 10 } {
            i < text.len() && text[i + 0] == const { b'0' + (EXP.abs_diff(0) % 10) }
        } else if const { EXP > -100 && EXP < 100 } {
            i + 1 < text.len()
                && text[i + 0] == const { b'0' + ((EXP.abs_diff(0) / 10) % 10) }
                && text[i + 1] == const { b'0' + ((EXP.abs_diff(0) / 1) % 10) }
        } else {
            i + 2 < text.len()
                && text[i + 0] == const { b'0' + ((EXP.abs_diff(0) / 100) % 10) }
                && text[i + 1] == const { b'0' + ((EXP.abs_diff(0) / 10) % 10) }
                && text[i + 2] == const { b'0' + ((EXP.abs_diff(0) / 1) % 10) }
        };

        let exp_dig_n = const {
            if EXP > -10 && EXP < 10 {
                1
            } else if EXP > -100 && EXP < 100 {
                2
            } else {
                3
            }
        };
        return if same_as_base {
            (self, i + exp_dig_n)
        } else {
            (Self::ZERO, 0)
        };
    }

    /// Continue parsing text after seeing the decimal separator at text[i - 1].
    /// The (integer) value v parsed thus far may be out of bounds.
    /// TODO: Permit fractions with an exponent.
    fn at_fraction(text: &[u8], start: usize, int_part: u64) -> (Self, usize) {
        // generic case with no fractional digits
        if const { EXP >= 0 } {
            return (Self::ZERO, 0);
        }

        // generic case with an integer component
        if const { EXP > -20 } {
            let mut i = start; // read index in text
            let end = start + const { (EXP as isize).strict_neg() as usize };

            // parse fractiononal value separately
            let mut frac_part: u64 = 0;
            // up to 19 digits can't overflow 64 bits
            while i < end {
                if i >= text.len() || !(b'0'..=b'9').contains(&text[i]) {
                    // TODO: lookup table
                    frac_part *= 10u64.pow((end - i) as u32);
                    break;
                }
                frac_part = frac_part * 10 + decimal_of(text[i]);
                i += 1;
            }

            let one = const {
                // redundant check needed for compiler
                if EXP < 0 && EXP > -20 {
                    let frac_n = (EXP as isize).strict_neg();
                    10u64.strict_pow(frac_n as u32)
                } else {
                    // not possible in this branch
                    42u64 // arbitrary placeholder
                }
            };
            let (count, carry) = one.carrying_mul(int_part, frac_part);
            return if carry == 0 {
                (count.into(), i)
            } else {
                (Self::ZERO, 0) // out of bounds
            };
        }

        // generic case with only fractional digits
        assert!(const { EXP < -19 });
        if int_part != 0 {
            return (Self::ZERO, 0); // out of bounds
        }
        // digit positions in text are all at a fixed location
        debug_assert_eq!(start, "0.".len());
        let end = const {
            // redundant check needed for compiler
            if EXP < 0 {
                "0.".len() + (EXP as isize).strict_neg() as usize
            } else {
                // not possible in this branch
                42 // arbitrary placeholder
            }
        };

        // pass mandatory zeroes, if EXP < -20
        let zero_until = const { (EXP as isize + 18).strict_neg() as usize };
        for i in 2..zero_until {
            if i >= text.len() || !(b'0'..=b'9').contains(&text[i]) {
                // non-siginificant fraction allowed
                return (Self::ZERO, i);
            }
            if text[i] != b'0' {
                // numeric overflow denied
                return (Self::ZERO, 0);
            }
        }

        // Delay appliance of the most significant digit because
        // the remaining 19 digits can't overflow 64 bits.
        let first_digit = decimal_of(text[zero_until]);
        let mut i = zero_until + 1; // read index
        let mut v: u64 = 0; // parsed value
        while i < end {
            if i >= text.len() || !(b'0'..=b'9').contains(&text[i]) {
                v *= 10u64.pow((end - i) as u32);
                break;
            }
            v = v * 10 + decimal_of(text[i]);
            i += 1;
        }

        // merge most significant digit with overflow protection
        let ms: u64 = 10_000_000_000_000_000_000;
        let (count, carry) = ms.carrying_mul(first_digit, v);
        return if carry == 0 {
            (count.into(), i)
        } else {
            (Self::ZERO, 0)
        };
    }

    /// Format the integer value as ASCII with leading zeroes.
    /// The usize return counts the number of leading zeroes,
    /// which can be up to 20 for Self::ZERO.
    fn count_digits(&self) -> ([Char; 20], usize) {
        // Initialize the result as "00000000000000000000".
        let mut buf: [Char; 20] = [Char::Digit0; 20];
        // The leading zero count equals the write index.
        let mut i = buf.len();

        let mut v = self.c;

        // print per two digits
        while v > 9 {
            let p = (v % 100) as usize * 2;
            v /= 100;

            i -= 2;
            buf[i + 0] = DOUBLE_DIGIT_TABLE[p + 0];
            buf[i + 1] = DOUBLE_DIGIT_TABLE[p + 1];
        }

        // print remainder digit, if any
        if v != 0 {
            let p = (v as usize * 2) + 1;
            i -= 1;
            buf[i] = DOUBLE_DIGIT_TABLE[p];
        }

        return (buf, i);
    }
}

#[cfg(test)]
mod text_tests {
    use super::*;

    #[test]
    fn parse_zero() {
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b""));
        assert_eq!((BaseCount::<0>::ZERO, 1), BaseCount::parse(b"0"));
        assert_eq!((BaseCount::<0>::ZERO, 3), BaseCount::parse(b"0E0"));
        assert_eq!((BaseCount::<1>::ZERO, 3), BaseCount::parse(b"0E1"));
        assert_eq!((BaseCount::<10>::ZERO, 4), BaseCount::parse(b"0E10"));
        assert_eq!((BaseCount::<127>::ZERO, 5), BaseCount::parse(b"0E127"));
        assert_eq!((BaseCount::<-1>::ZERO, 4), BaseCount::parse(b"0E-1"));
        assert_eq!((BaseCount::<-10>::ZERO, 5), BaseCount::parse(b"0E-10"));
        assert_eq!((BaseCount::<-128>::ZERO, 6), BaseCount::parse(b"0E-128"));
    }

    #[test]
    fn illegal_lead() {
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"00"));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"01"));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"00."));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"01."));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"00.0"));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"01.0"));
        assert_eq!((BaseCount::<0>::ZERO, 0), BaseCount::parse(b"00.1"));

        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"00"));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"01"));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"00."));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"01."));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"00.0"));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"01.0"));
        assert_eq!((BaseCount::<1>::ZERO, 0), BaseCount::parse(b"00.1"));

        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b""));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"00"));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"01"));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"00."));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"01."));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"00.0"));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"01.0"));
        assert_eq!((BaseCount::<-1>::ZERO, 0), BaseCount::parse(b"00.1"));
    }

    #[test]
    fn parse_integer() {
        assert_eq!((BaseCount::<0>::from(123), 3), BaseCount::parse(b"123"));
        assert_eq!((BaseCount::<-1>::from(1230), 3), BaseCount::parse(b"123"));
        assert_eq!((BaseCount::<-2>::from(12300), 3), BaseCount::parse(b"123"));
    }

    #[test]
    fn bases_of_one_million() {
        let text = b"1000000";

        assert_eq!((BaseCount::<0>::from(1_000_000), 7), BaseCount::parse(text));
        assert_eq!((BaseCount::<1>::from(100_000), 7), BaseCount::parse(text));
        // …
        assert_eq!((BaseCount::<5>::from(10), 7), BaseCount::parse(text));
        assert_eq!((BaseCount::<6>::from(1), 7), BaseCount::parse(text));

        // deny resolutions over one million
        assert_eq!((BaseCount::<7>::ZERO, 0), BaseCount::parse(text));
        assert_eq!((BaseCount::<8>::ZERO, 0), BaseCount::parse(text));
        assert_eq!((BaseCount::<30>::ZERO, 0), BaseCount::parse(text));

        // fractions permitted
        assert_eq!(
            (BaseCount::<-1>::from(10_000_000), 7),
            BaseCount::parse(text)
        );
        assert_eq!(
            (BaseCount::<-2>::from(100_000_000), 7),
            BaseCount::parse(text)
        );
        // …
        assert_eq!(
            (BaseCount::<-12>::from(1_000_000_000_000_000_000), 7),
            BaseCount::parse(text)
        );
        assert_eq!(
            (BaseCount::<-13>::from(10_000_000_000_000_000_000), 7),
            BaseCount::parse(text)
        );

        // exceed BaseCount::MAX with too many fractions
        assert_eq!((BaseCount::<-14>::ZERO, 0), BaseCount::parse(text));
        assert_eq!((BaseCount::<-15>::ZERO, 0), BaseCount::parse(text));
        assert_eq!((BaseCount::<-30>::ZERO, 0), BaseCount::parse(text));
    }
}

impl<const EXP: i8> fmt::Display for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.c == 0 {
            return f.write_str("0");
        }

        if const { EXP > 0 } {
            return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f);
        }

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

        let (buf, i) = self.count_digits();

        if const { EXP == 0 } {
            f.write_str(buf[i..].as_str())?;
        }

        if const { EXP < -19 } {
            f.write_str("0.")?;
            write_n_zeroes(f, (-20 - EXP) as usize)?;
            return f.write_str(buf.as_str());
        }

        assert!(const { EXP < 0 && EXP > -20 });

        if i < const { (EXP + 20) as usize } {
            f.write_str(buf[i..const { (EXP + 20) as usize }].as_str())?;
            f.write_str(".")?;
        } else {
            f.write_str("0.")?;
        }
        return f.write_str(buf[const { (EXP + 20) as usize }..].as_str());
    }
}

impl<const EXP: i8> fmt::Debug for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f);
    }
}

impl<const EXP: i8> fmt::LowerExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{0}e{EXP}", self.c)
    }
}

impl<const EXP: i8> fmt::UpperExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{0}E{EXP}", self.c)
    }
}

#[inline(always)]
fn decimal_of(c: u8) -> u64 {
    return c as u64 - b'0' as u64;
}

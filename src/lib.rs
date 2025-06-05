use std::convert::From;
use std::fmt;
use std::mem::MaybeUninit;
use std::slice;
use std::str::from_utf8_unchecked;

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
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Hash)]
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
/// let previous = Century::map_u64(1900).unwrap();
/// assert_eq!(19, u64::from(previous));
/// ```
impl<const EXP: i8> From<BaseCount<EXP>> for u64 {
    /// Decouple the count from the base component.
    fn from(c: BaseCount<EXP>) -> u64 {
        return c.c;
    }
}

impl<const EXP: i8> BaseCount<EXP> {
    /// Count 0 is the smallest value in range.
    pub const ZERO: Self = Self { c: 0 };

    /// Count 1 is the second smallest value in range, a.k.a. the resultion.
    ///
    /// ```
    /// let pi = b10::Centi::from(314);
    /// let (lt, _) = pi.add(b10::Centi::ONE);
    /// let (gt, _) = pi.sub(b10::Centi::ONE);
    /// assert_eq!(
    ///     "π in range (3.13, 3.15)",
    ///     format!("π in range ({gt}, {lt})"),
    /// );
    /// ```
    pub const ONE: Self = Self { c: 1 };

    /// Count [u64::MAX] is the largest value in range.
    pub const MAX: Self = Self { c: u64::MAX };

    /// Get numeric value n iff an exact match within the base exponent exists,
    /// and iff the numeric value is in range [Self::MAX].
    ///
    /// ```
    /// use b10::{Centi, Kilo};
    ///
    /// assert_eq!(Some(Centi::from(200)), Centi::map_u64(2));
    /// assert_eq!(Some(Kilo::from(5)), Kilo::map_u64(5000));
    ///
    /// // range protection
    /// assert_eq!(None, Centi::map_u64(u64::MAX));
    /// // loss-of-precision protection
    /// assert_eq!(None, Kilo::map_u64(5100));
    /// ```
    pub fn map_u64(n: u64) -> Option<Self> {
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
        match const { R as isize - EXP as isize } {
            // same base; same count
            0 => Some(self.c.into()),

            // 21 decimals or more causes a conversion ratio beyond u64::MAX
            ..=-21 | 21.. => {
                if self == Self::ZERO {
                    Some(BaseCount::<R>::ZERO)
                } else {
                    None
                }
            }

            // lower base; raise count with a power of ten
            -20..0 => {
                let (ratio, max_in) = const {
                    let add_dec_n = EXP as i32 - R as i32;
                    // redundant check needed by compiler
                    if add_dec_n >= 1 && add_dec_n <= 20 {
                        let ratio = 10u64.pow(add_dec_n as u32);
                        (ratio, u64::MAX / ratio)
                    } else {
                        (1, 1) // placeholder for unreachable
                    }
                };
                // ensure unreachable above is actually unreachable
                assert_ne!(max_in, 1);
                if self.c <= max_in {
                    Some(BaseCount::<R> { c: self.c * ratio })
                } else {
                    None // rebase overflows Self::MAX
                }
            }

            // higher base; lower count with a power of ten
            1..=20 => {
                let ratio = const {
                    let drop_dec_n = R as i32 - EXP as i32;
                    // redundant check needed by compiler
                    if drop_dec_n >= 1 && drop_dec_n <= 20 {
                        10u64.pow(drop_dec_n as u32)
                    } else {
                        1 // placeholder for unreachable
                    }
                };
                // ensure unreachable above is actually unreachable
                assert_ne!(ratio, 1);
                if self.c % ratio == 0 {
                    Some(BaseCount::<R> { c: self.c / ratio })
                } else {
                    None // loss-of precision denied
                }
            }
        }
    }

    /// Get [Self::ONE] added to self, or None when [Self::MAX].
    ///
    /// ```
    /// assert_eq!(b10::Centi::from(10).inc(), "0.11".parse().ok());
    /// ```
    #[inline(always)]
    pub fn inc(self) -> Option<Self> {
        match self.c.checked_add(1) {
            None => None,
            Some(sum) => Some(Self { c: sum }),
        }
    }

    /// Get [Self::ONE] subtracted from self, or None when [Self::ZERO].
    ///
    /// ```
    /// assert_eq!(b10::Centi::from(10).dec(), "0.09".parse().ok());
    /// ```
    #[inline(always)]
    pub fn dec(self) -> Option<Self> {
        match self.c.checked_sub(1) {
            None => None,
            Some(diff) => Some(Self { c: diff }),
        }
    }

    /// Iterate incremental. The count starts at self plus [Self::ONE].
    pub fn asc(self) -> Ascending<EXP> {
        Ascending { from: self }
    }

    /// Iterate decremental. The countdown starts at self minus [Self::ONE].
    pub fn desc(self) -> Descending<EXP> {
        Descending { from: self }
    }

    /// Get the sum of both counts including an overflow flag. For any pair of
    /// arguments, self + summand = sum + overflow, in which overflow is 2⁶⁴
    /// times [Self::ONE] when `true`, or 0 when `false`.
    #[inline(always)]
    pub fn add(self, summand: Self) -> (Self, bool) {
        let (sum, overflow) = self.c.overflowing_add(summand.c);
        return (Self { c: sum }, overflow);
    }

    /// Get the difference between both counts including a negative flag. For
    /// any pair of arguments, self − subtrahend = difference × negative, in
    /// which negative is −1 when `true`, or 1 when `false`.
    ///
    /// ```
    /// let (a, b): (b10::Deca, b10::Deca) = (7.into(), 9.into());
    /// assert_eq!(
    ///     "7E1 − 9E1 = (2E1, true)",
    ///     format!("{a:?} − {b:?} = {0:?}", a.sub(b)),
    /// );
    /// // zero is not negative
    /// assert_eq!(
    ///     "7E1 − 7E1 = (0E1, false)",
    ///     format!("{a:?} − {a:?} = {0:?}", a.sub(a)),
    /// );
    /// ```
    #[inline(always)]
    pub fn sub(self, subtrahend: Self) -> (Self, bool) {
        if self >= subtrahend {
            ((self.c - subtrahend.c).into(), false)
        } else {
            ((subtrahend.c - self.c).into(), true)
        }
    }

    /// Get the product of both counts, including 64-bit overflow. For any pair
    /// of arguments, self × multiplicant = product + (overflow × 2⁶⁴).
    /// A compile-time check guarantees that generic P is equal to EXP + M.
    ///
    /// ```
    /// use b10::{Milli, Nano, Pico};
    ///
    /// let mA = Milli::from(100);
    /// let ns = Nano::from(4);
    ///
    /// let (pC, overflow):(Pico, Pico) = mA.mul(ns);
    /// if overflow != Pico::ZERO {
    ///     panic!("too much for pico");
    /// }
    /// assert_eq!(
    ///     "100E-3 × 4E-9 = 400E-12",
    ///     format!("{mA:E} × {ns:E} = {pC:E}"),
    /// );
    /// ```
    ///
    /// 🚧 Generic constant P is needed because “const parameters may only
    /// appear as a standalone argument inside of a type” at the moment. An
    /// alternative is expected once a return of `BaseCount<{ EXP + M }>` or
    /// something similar will be allowed. See `feature(generic_const_exprs)` at
    /// <https://github.com/rust-lang/rust/issues/76560> for more detail.
    #[cfg(feature = "redundant_generics")]
    #[inline(always)]
    pub fn mul<const M: i8, const P: i8>(
        self,
        multiplicant: BaseCount<M>,
    ) -> (BaseCount<P>, BaseCount<P>) {
        // compile-time check
        const {
            if P != EXP + M {
                panic!("generic EXP plus M does not equal P");
            }
        }
        let wide = u128::from(self.c) * u128::from(multiplicant.c);
        let product = wide & u64::MAX as u128;
        let overflow = wide >> 64;
        return ((product as u64).into(), (overflow as u64).into());
    }

    /// Get the product of self and MULTIPLICANT, including 64-bit overflow. For
    /// any pair of arguments, self × MULTIPLICANT = product + (overflow × 2⁶⁴).
    ///
    /// ```
    /// let x = b10::BaseCount::<-3>::from(2997);
    /// const dozen: u64 = 12;
    /// let (product, overflow) = x.mul_const::<dozen>();
    /// assert_eq!(
    ///     "12 × 2.997 = 35.964 + (0.000 × 2⁶⁴)",
    ///     format!("{dozen} × {x} = {product} + ({overflow} × 2⁶⁴)"),
    /// );
    /// ```
    #[inline(always)]
    pub fn mul_const<const MULTIPLICANT: u64>(self) -> (Self, Self) {
        let wide = u128::from(self.c) * u128::from(MULTIPLICANT);
        let product = wide & u64::MAX as u128;
        let overflow = wide >> 64;
        return ((product as u64).into(), (overflow as u64).into());
    }

    /// Get the quotient and the remainder for divisor, with None for division
    /// by zero. D must greater or equal to EXP. The constraint prevents numeric
    /// overflows by design.
    ///
    /// ```
    /// let price = b10::BaseCount::<-2>::from(100420);
    /// let fifty = b10::Natural::from(50);
    ///
    /// let (part, rem) = price.div(fifty).unwrap();
    /// assert_eq!(
    ///     "1004.20 ÷ 50 is 20 with 4.20 remaining",
    ///     format!("{price} ÷ {fifty} is {part} with {rem} remaining"),
    /// );
    /// ```
    #[inline(always)]
    pub fn div<const D: i8>(self, divisor: BaseCount<D>) -> Option<(u64, Self)> {
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

    /// Get the quotient and the remainder for DIVISOR.
    ///
    /// ```
    /// let price = b10::BaseCount::<-2>::from(299);
    /// let (half, remainder) = price.div_const::<2>();
    /// assert_eq!(
    ///     "½ of 2.99 is 1.49 with 0.01 remaining",
    ///     format!("½ of {price} is {half} with {remainder} remaining"),
    /// );
    /// ```
    #[inline(always)]
    pub fn div_const<const DIVISOR: u64>(self) -> (Self, Self) {
        const {
            if DIVISOR == 0 {
                panic!("zero divisor denied");
            }
        }
        ((self.c / DIVISOR).into(), (self.c % DIVISOR).into())
    }

    /// Get the exponentiation of self with a constant POWER. The return is None
    /// when a numeric overflow occurred.
    ///
    /// ```
    /// let rib = b10::Milli::from(12);
    /// let square = rib.pow_const::<2, -6>().unwrap();
    /// let cube = rib.pow_const::<3, -9>().unwrap();
    /// assert_eq!(
    ///     "0.012² = 0.000144",
    ///     format!("{rib}² = {square}"),
    /// );
    /// assert_eq!(
    ///     "0.012³ = 0.000001728",
    ///     format!("{rib}³ = {cube}"),
    /// );
    /// ```
    ///
    /// 🚧 Generic constant P is needed because “const parameters may only
    /// appear as a standalone argument inside of a type” at the moment. An
    /// alternative is expected once a return of `BaseCount<{ EXP * POWER }>` or
    /// something similar will be allowed. See `feature(generic_const_exprs)` at
    /// <https://github.com/rust-lang/rust/issues/76560> for more detail.
    #[cfg(feature = "redundant_generics")]
    #[inline(always)]
    pub fn pow_const<const POWER: u32, const P: i8>(self) -> Option<BaseCount<P>> {
        // compile-time checks
        const {
            if POWER == 0 {
                panic!("to the power of 0 always is 1")
            }
            if POWER == 1 {
                panic!("to the power of 1 is a no-op")
            }
            if POWER as i64 * EXP as i64 != P as i64 {
                panic!("generic POWER times EXP does not equal P");
            }
        }
        match self.c.checked_pow(POWER) {
            None => None,
            Some(p) => Some(p.into()),
        }
    }

    /// Get the base-10 logarithm, rounded down [toward negative infinity].
    ///
    /// ```
    /// assert_eq!(b10::Mega::ONE.log10_floor(), Some(6), "⌊log₁₀(10⁶)⌋");
    /// assert_eq!(b10::Micro::ONE.log10_floor(), Some(-6), "⌊log₁₀(10⁻⁶)⌋");
    ///
    /// let pi = b10::Centi::from(314);
    /// assert_eq!(pi.log10_floor(), Some(0), "⌊log₁₀(π)⌋");
    /// let pi_float: f64 = 3.14;
    /// assert_eq!(pi_float.log10(), 0.49692964807321494, "f64 reference");
    ///
    /// let planck = b10::BaseCount::<-42>::from(662607015);
    /// assert_eq!(planck.log10_floor(), Some(-34), "⌊log₁₀(ℎ)⌋");
    /// let planck_float: f64 = 6.62607015E-34;
    /// assert_eq!(planck_float.log10(), -33.17874397056745, "f64 reference");
    /// ```
    pub fn log10_floor(self) -> Option<i32> {
        match self.c.checked_ilog10() {
            None => None,
            Some(l) => Some(l as i32 + const { EXP as i32 }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constants() {
        assert_eq!(0 as u64, Kilo::ZERO.into());
        assert_eq!(1 as u64, Kilo::ONE.into());
        assert_eq!(u64::MAX, Kilo::MAX.into());

        assert!(Kilo::ONE > Kilo::ZERO);
        assert!(Kilo::MAX > Kilo::ONE);

        #[cfg(feature = "redundant_generics")]
        assert_eq!(
            (Kilo::MAX, Kilo::ZERO),
            Kilo::ONE.mul(Natural::from(u64::MAX))
        );
    }

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

        // below Self::ONE
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

    #[test]
    fn overflows() {
        assert_eq!((Deci::from(6), true), Deci::MAX.add(Deci::from(7)));

        #[cfg(feature = "redundant_generics")]
        assert_eq!(
            Natural::from(1 << 40).mul(Natural::from(1 << 40)),
            (Natural::ZERO, Natural::from(1 << (40 + 40 - 64))),
        );
        assert_eq!(
            Natural::from(1 << 40).mul_const::<{ 1 << 40 }>(),
            (Natural::ZERO, Natural::from(1 << (40 + 40 - 64))),
        );

        #[cfg(feature = "redundant_generics")]
        assert_eq!(Natural::from(1 << 40).pow_const::<2, 0>(), None,);
    }

    #[test]
    #[cfg(feature = "redundant_generics")]
    fn product() {
        assert_eq!(
            (Natural::from(6), Natural::ZERO),
            Natural::from(2).mul(Natural::from(3))
        );
    }

    #[test]
    fn log10_floor() {
        assert_eq!(Milli::from(0).log10_floor(), None, "0.000");
        assert_eq!(Milli::from(1).log10_floor(), Some(-3), "0.001");
        // …
        assert_eq!(Milli::from(9).log10_floor(), Some(-3), "0.009");
        assert_eq!(Milli::from(10).log10_floor(), Some(-2), "0.010");
        assert_eq!(Milli::from(11).log10_floor(), Some(-2), "0.011");
        // …
        assert_eq!(Milli::from(99).log10_floor(), Some(-2), "0.099");
        assert_eq!(Milli::from(100).log10_floor(), Some(-1), "0.100");
        assert_eq!(Milli::from(101).log10_floor(), Some(-1), "0.101");
        // …
        assert_eq!(Milli::from(999).log10_floor(), Some(-1), "0.999");
        assert_eq!(Milli::from(1_000).log10_floor(), Some(0), "1.000");
        assert_eq!(Milli::from(1_001).log10_floor(), Some(0), "1.001");
        // …
        assert_eq!(Milli::from(9_999).log10_floor(), Some(0), "9.999");
        assert_eq!(Milli::from(10_000).log10_floor(), Some(1), "10.000");
        assert_eq!(Milli::from(10_001).log10_floor(), Some(1), "10.001");
        // …

        assert_eq!(
            BaseCount::<{ i8::MIN }>::ONE.log10_floor(),
            Some(-128),
            "smallest BaseCount",
        );
        assert_eq!(
            BaseCount::<{ i8::MAX }>::from(u64::MAX).log10_floor(),
            Some(146),
            "largest BaseCount",
        );
    }
}

/// Textual Representation
impl<const EXP: i8> BaseCount<EXP> {
    /// Get an exact reading of the numeric value at the start of text. The
    /// `usize` in return has the number of octets parsed, which may be less
    /// than the slice length! Parsing is robust against malicious input. No
    /// assumptions are made on the byte content of text. Most usecases will
    /// benefit from the more straightforward [str::parse] instead.
    ///
    /// ```
    /// assert_eq!("0.001".parse(), Ok(b10::Milli::ONE));
    /// ```
    ///
    /// ASCII character "." (0x2E) is recognised as a decimal separator. ASCII
    /// character "E" (0x45) and "e" (0x65) are both accepted for E notation.
    /// Non-significant digits (a.k.a. leading zeroes) are ignored/permitted.
    /// The following cases get rejected with a zero usize.
    ///
    ///  * No input: empty text slice
    ///  * Range exhaustion: any numeric value above Self::MAX
    ///  * Beyond resolution: significant digits beneath Self::ONE
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

        // TODO: use rebase once generic const expressions are supported

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
                b'0'..=b'9' => {
                    let digit = c as u64 - b'0' as u64;
                    if num >= u64::MAX / 10 && (num > u64::MAX / 10 || digit > 5) {
                        // numeric overflow
                        return (0, 0, 0);
                    }
                    num = num * 10 + digit;
                }

                // decimal separator
                b'.' => {
                    if fraction_offset != 0 {
                        // two separators
                        return (0, 0, 0);
                    }
                    fraction_offset = i + 1;
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

    fn fmt_metric_prefix(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match const { EXP } {
            31.. => write!(f, "{self:E}"),

            30 => write!(f, "{} Q", BaseCount::<0>::from(self.c)),
            29 => write!(f, "{} Q", BaseCount::<-1>::from(self.c)),
            28 => write!(f, "{} Q", BaseCount::<-2>::from(self.c)),

            27 => write!(f, "{} R", BaseCount::<0>::from(self.c)),
            26 => write!(f, "{} R", BaseCount::<-1>::from(self.c)),
            25 => write!(f, "{} R", BaseCount::<-2>::from(self.c)),

            24 => write!(f, "{} Y", BaseCount::<0>::from(self.c)),
            23 => write!(f, "{} Y", BaseCount::<-1>::from(self.c)),
            22 => write!(f, "{} Y", BaseCount::<-2>::from(self.c)),

            21 => write!(f, "{} Z", BaseCount::<0>::from(self.c)),
            20 => write!(f, "{} Z", BaseCount::<-1>::from(self.c)),
            19 => write!(f, "{} Z", BaseCount::<-2>::from(self.c)),

            18 => write!(f, "{} E", BaseCount::<0>::from(self.c)),
            17 => write!(f, "{} E", BaseCount::<-1>::from(self.c)),
            16 => write!(f, "{} E", BaseCount::<-2>::from(self.c)),

            15 => write!(f, "{} P", BaseCount::<0>::from(self.c)),
            14 => write!(f, "{} P", BaseCount::<-1>::from(self.c)),
            13 => write!(f, "{} P", BaseCount::<-2>::from(self.c)),

            12 => write!(f, "{} T", BaseCount::<0>::from(self.c)),
            11 => write!(f, "{} T", BaseCount::<-1>::from(self.c)),
            10 => write!(f, "{} T", BaseCount::<-2>::from(self.c)),

            9 => write!(f, "{} G", BaseCount::<0>::from(self.c)),
            8 => write!(f, "{} G", BaseCount::<-1>::from(self.c)),
            7 => write!(f, "{} G", BaseCount::<-2>::from(self.c)),

            6 => write!(f, "{} M", BaseCount::<0>::from(self.c)),
            5 => write!(f, "{} M", BaseCount::<-1>::from(self.c)),
            4 => write!(f, "{} M", BaseCount::<-2>::from(self.c)),

            3 => write!(f, "{} k", BaseCount::<0>::from(self.c)),
            2 => write!(f, "{} h", BaseCount::<0>::from(self.c)),
            1 => write!(f, "{} da", BaseCount::<0>::from(self.c)),
            0 => write!(f, "{}", BaseCount::<0>::from(self.c)),
            -1 => write!(f, "{} d", BaseCount::<0>::from(self.c)),
            -2 => write!(f, "{} c", BaseCount::<0>::from(self.c)),

            -3 => write!(f, "{} m", BaseCount::<0>::from(self.c)),
            -4 => write!(f, "{} m", BaseCount::<-1>::from(self.c)),
            -5 => write!(f, "{} m", BaseCount::<-2>::from(self.c)),

            -6 => write!(f, "{} µ", BaseCount::<0>::from(self.c)),
            -7 => write!(f, "{} µ", BaseCount::<-1>::from(self.c)),
            -8 => write!(f, "{} µ", BaseCount::<-2>::from(self.c)),

            -9 => write!(f, "{} n", BaseCount::<0>::from(self.c)),
            -10 => write!(f, "{} n", BaseCount::<-1>::from(self.c)),
            -11 => write!(f, "{} n", BaseCount::<-2>::from(self.c)),

            -12 => write!(f, "{} p", BaseCount::<0>::from(self.c)),
            -13 => write!(f, "{} p", BaseCount::<-1>::from(self.c)),
            -14 => write!(f, "{} p", BaseCount::<-2>::from(self.c)),

            -15 => write!(f, "{} f", BaseCount::<0>::from(self.c)),
            -16 => write!(f, "{} f", BaseCount::<-1>::from(self.c)),
            -17 => write!(f, "{} f", BaseCount::<-2>::from(self.c)),

            -18 => write!(f, "{} a", BaseCount::<0>::from(self.c)),
            -19 => write!(f, "{} a", BaseCount::<-1>::from(self.c)),
            -20 => write!(f, "{} a", BaseCount::<-2>::from(self.c)),

            -21 => write!(f, "{} z", BaseCount::<0>::from(self.c)),
            -22 => write!(f, "{} z", BaseCount::<-1>::from(self.c)),
            -23 => write!(f, "{} z", BaseCount::<-2>::from(self.c)),

            -24 => write!(f, "{} y", BaseCount::<0>::from(self.c)),
            -25 => write!(f, "{} y", BaseCount::<-1>::from(self.c)),
            -26 => write!(f, "{} y", BaseCount::<-2>::from(self.c)),

            -27 => write!(f, "{} r", BaseCount::<0>::from(self.c)),
            -28 => write!(f, "{} r", BaseCount::<-1>::from(self.c)),
            -29 => write!(f, "{} r", BaseCount::<-2>::from(self.c)),

            -30 => write!(f, "{} q", BaseCount::<0>::from(self.c)),
            -31 => write!(f, "{} q", BaseCount::<-1>::from(self.c)),
            -32 => write!(f, "{} q", BaseCount::<-2>::from(self.c)),
            -33 => write!(f, "{} q", BaseCount::<-3>::from(self.c)),
            -34 => write!(f, "{} q", BaseCount::<-4>::from(self.c)),
            -35 => write!(f, "{} q", BaseCount::<-5>::from(self.c)),
            -36 => write!(f, "{} q", BaseCount::<-6>::from(self.c)),
            -37 => write!(f, "{} q", BaseCount::<-7>::from(self.c)),
            -38 => write!(f, "{} q", BaseCount::<-8>::from(self.c)),
            -39 => write!(f, "{} q", BaseCount::<-9>::from(self.c)),

            -40 => write!(f, "{} q", BaseCount::<-10>::from(self.c)),
            -41 => write!(f, "{} q", BaseCount::<-11>::from(self.c)),
            -42 => write!(f, "{} q", BaseCount::<-12>::from(self.c)),
            -43 => write!(f, "{} q", BaseCount::<-13>::from(self.c)),
            -44 => write!(f, "{} q", BaseCount::<-14>::from(self.c)),
            -45 => write!(f, "{} q", BaseCount::<-15>::from(self.c)),
            -46 => write!(f, "{} q", BaseCount::<-16>::from(self.c)),
            -47 => write!(f, "{} q", BaseCount::<-17>::from(self.c)),
            -48 => write!(f, "{} q", BaseCount::<-18>::from(self.c)),
            -49 => write!(f, "{} q", BaseCount::<-19>::from(self.c)),

            -50 => write!(f, "{} q", BaseCount::<-20>::from(self.c)),
            -51 => write!(f, "{} q", BaseCount::<-21>::from(self.c)),
            -52 => write!(f, "{} q", BaseCount::<-22>::from(self.c)),
            -53 => write!(f, "{} q", BaseCount::<-23>::from(self.c)),
            -54 => write!(f, "{} q", BaseCount::<-24>::from(self.c)),
            -55 => write!(f, "{} q", BaseCount::<-25>::from(self.c)),
            -56 => write!(f, "{} q", BaseCount::<-26>::from(self.c)),
            -57 => write!(f, "{} q", BaseCount::<-27>::from(self.c)),
            -58 => write!(f, "{} q", BaseCount::<-28>::from(self.c)),
            -59 => write!(f, "{} q", BaseCount::<-29>::from(self.c)),

            -60 => write!(f, "{} q", BaseCount::<-30>::from(self.c)),
            -61 => write!(f, "{} q", BaseCount::<-31>::from(self.c)),
            -62 => write!(f, "{} q", BaseCount::<-32>::from(self.c)),
            -63 => write!(f, "{} q", BaseCount::<-33>::from(self.c)),
            -64 => write!(f, "{} q", BaseCount::<-34>::from(self.c)),
            -65 => write!(f, "{} q", BaseCount::<-35>::from(self.c)),
            -66 => write!(f, "{} q", BaseCount::<-36>::from(self.c)),
            -67 => write!(f, "{} q", BaseCount::<-37>::from(self.c)),
            -68 => write!(f, "{} q", BaseCount::<-38>::from(self.c)),
            -69 => write!(f, "{} q", BaseCount::<-39>::from(self.c)),

            -70 => write!(f, "{} q", BaseCount::<-40>::from(self.c)),
            -71 => write!(f, "{} q", BaseCount::<-41>::from(self.c)),
            -72 => write!(f, "{} q", BaseCount::<-42>::from(self.c)),
            -73 => write!(f, "{} q", BaseCount::<-43>::from(self.c)),
            -74 => write!(f, "{} q", BaseCount::<-44>::from(self.c)),
            -75 => write!(f, "{} q", BaseCount::<-45>::from(self.c)),
            -76 => write!(f, "{} q", BaseCount::<-46>::from(self.c)),
            -77 => write!(f, "{} q", BaseCount::<-47>::from(self.c)),
            -78 => write!(f, "{} q", BaseCount::<-48>::from(self.c)),
            -79 => write!(f, "{} q", BaseCount::<-49>::from(self.c)),

            -80 => write!(f, "{} q", BaseCount::<-50>::from(self.c)),
            -81 => write!(f, "{} q", BaseCount::<-51>::from(self.c)),
            -82 => write!(f, "{} q", BaseCount::<-52>::from(self.c)),
            -83 => write!(f, "{} q", BaseCount::<-53>::from(self.c)),
            -84 => write!(f, "{} q", BaseCount::<-54>::from(self.c)),
            -85 => write!(f, "{} q", BaseCount::<-55>::from(self.c)),
            -86 => write!(f, "{} q", BaseCount::<-56>::from(self.c)),
            -87 => write!(f, "{} q", BaseCount::<-57>::from(self.c)),
            -88 => write!(f, "{} q", BaseCount::<-58>::from(self.c)),
            -89 => write!(f, "{} q", BaseCount::<-59>::from(self.c)),

            -90 => write!(f, "{} q", BaseCount::<-60>::from(self.c)),
            -91 => write!(f, "{} q", BaseCount::<-61>::from(self.c)),
            -92 => write!(f, "{} q", BaseCount::<-62>::from(self.c)),
            -93 => write!(f, "{} q", BaseCount::<-63>::from(self.c)),
            -94 => write!(f, "{} q", BaseCount::<-64>::from(self.c)),
            -95 => write!(f, "{} q", BaseCount::<-65>::from(self.c)),
            -96 => write!(f, "{} q", BaseCount::<-66>::from(self.c)),
            -97 => write!(f, "{} q", BaseCount::<-67>::from(self.c)),
            -98 => write!(f, "{} q", BaseCount::<-68>::from(self.c)),
            -99 => write!(f, "{} q", BaseCount::<-69>::from(self.c)),

            -100 => write!(f, "{} q", BaseCount::<-70>::from(self.c)),
            -101 => write!(f, "{} q", BaseCount::<-71>::from(self.c)),
            -102 => write!(f, "{} q", BaseCount::<-72>::from(self.c)),
            -103 => write!(f, "{} q", BaseCount::<-73>::from(self.c)),
            -104 => write!(f, "{} q", BaseCount::<-74>::from(self.c)),
            -105 => write!(f, "{} q", BaseCount::<-75>::from(self.c)),
            -106 => write!(f, "{} q", BaseCount::<-76>::from(self.c)),
            -107 => write!(f, "{} q", BaseCount::<-77>::from(self.c)),
            -108 => write!(f, "{} q", BaseCount::<-78>::from(self.c)),
            -109 => write!(f, "{} q", BaseCount::<-79>::from(self.c)),

            -110 => write!(f, "{} q", BaseCount::<-80>::from(self.c)),
            -111 => write!(f, "{} q", BaseCount::<-81>::from(self.c)),
            -112 => write!(f, "{} q", BaseCount::<-82>::from(self.c)),
            -113 => write!(f, "{} q", BaseCount::<-83>::from(self.c)),
            -114 => write!(f, "{} q", BaseCount::<-84>::from(self.c)),
            -115 => write!(f, "{} q", BaseCount::<-85>::from(self.c)),
            -116 => write!(f, "{} q", BaseCount::<-86>::from(self.c)),
            -117 => write!(f, "{} q", BaseCount::<-87>::from(self.c)),
            -118 => write!(f, "{} q", BaseCount::<-88>::from(self.c)),
            -119 => write!(f, "{} q", BaseCount::<-89>::from(self.c)),

            -120 => write!(f, "{} q", BaseCount::<-90>::from(self.c)),
            -121 => write!(f, "{} q", BaseCount::<-91>::from(self.c)),
            -122 => write!(f, "{} q", BaseCount::<-92>::from(self.c)),
            -123 => write!(f, "{} q", BaseCount::<-93>::from(self.c)),
            -124 => write!(f, "{} q", BaseCount::<-94>::from(self.c)),
            -125 => write!(f, "{} q", BaseCount::<-95>::from(self.c)),
            -126 => write!(f, "{} q", BaseCount::<-96>::from(self.c)),
            -127 => write!(f, "{} q", BaseCount::<-97>::from(self.c)),
            -128 => write!(f, "{} q", BaseCount::<-98>::from(self.c)),
        }
    }

    const fn upper_exp() -> &'static str {
        match const { EXP } {
            0 => "E0",
            1 => "E1",
            2 => "E2",
            3 => "E3",
            4 => "E4",
            5 => "E5",
            6 => "E6",
            7 => "E7",
            8 => "E8",
            9 => "E9",

            10 => "E10",
            11 => "E11",
            12 => "E12",
            13 => "E13",
            14 => "E14",
            15 => "E15",
            16 => "E16",
            17 => "E17",
            18 => "E18",
            19 => "E19",

            20 => "E20",
            21 => "E21",
            22 => "E22",
            23 => "E23",
            24 => "E24",
            25 => "E25",
            26 => "E26",
            27 => "E27",
            28 => "E28",
            29 => "E29",

            30 => "E30",
            31 => "E31",
            32 => "E32",
            33 => "E33",
            34 => "E34",
            35 => "E35",
            36 => "E36",
            37 => "E37",
            38 => "E38",
            39 => "E39",

            40 => "E40",
            41 => "E41",
            42 => "E42",
            43 => "E43",
            44 => "E44",
            45 => "E45",
            46 => "E46",
            47 => "E47",
            48 => "E48",
            49 => "E49",

            50 => "E50",
            51 => "E51",
            52 => "E52",
            53 => "E53",
            54 => "E54",
            55 => "E55",
            56 => "E56",
            57 => "E57",
            58 => "E58",
            59 => "E59",

            60 => "E60",
            61 => "E61",
            62 => "E62",
            63 => "E63",
            64 => "E64",
            65 => "E65",
            66 => "E66",
            67 => "E67",
            68 => "E68",
            69 => "E69",

            70 => "E70",
            71 => "E71",
            72 => "E72",
            73 => "E73",
            74 => "E74",
            75 => "E75",
            76 => "E76",
            77 => "E77",
            78 => "E78",
            79 => "E79",

            80 => "E80",
            81 => "E81",
            82 => "E82",
            83 => "E83",
            84 => "E84",
            85 => "E85",
            86 => "E86",
            87 => "E87",
            88 => "E88",
            89 => "E89",

            90 => "E90",
            91 => "E91",
            92 => "E92",
            93 => "E93",
            94 => "E94",
            95 => "E95",
            96 => "E96",
            97 => "E97",
            98 => "E98",
            99 => "E99",

            100 => "E100",
            101 => "E101",
            102 => "E102",
            103 => "E103",
            104 => "E104",
            105 => "E105",
            106 => "E106",
            107 => "E107",
            108 => "E108",
            109 => "E109",

            110 => "E110",
            111 => "E111",
            112 => "E112",
            113 => "E113",
            114 => "E114",
            115 => "E115",
            116 => "E116",
            117 => "E117",
            118 => "E118",
            119 => "E119",

            120 => "E120",
            121 => "E121",
            122 => "E122",
            123 => "E123",
            124 => "E124",
            125 => "E125",
            126 => "E126",
            127 => "E127",

            -1 => "E-1",
            -2 => "E-2",
            -3 => "E-3",
            -4 => "E-4",
            -5 => "E-5",
            -6 => "E-6",
            -7 => "E-7",
            -8 => "E-8",
            -9 => "E-9",

            -10 => "E-10",
            -11 => "E-11",
            -12 => "E-12",
            -13 => "E-13",
            -14 => "E-14",
            -15 => "E-15",
            -16 => "E-16",
            -17 => "E-17",
            -18 => "E-18",
            -19 => "E-19",

            -20 => "E-20",
            -21 => "E-21",
            -22 => "E-22",
            -23 => "E-23",
            -24 => "E-24",
            -25 => "E-25",
            -26 => "E-26",
            -27 => "E-27",
            -28 => "E-28",
            -29 => "E-29",

            -30 => "E-30",
            -31 => "E-31",
            -32 => "E-32",
            -33 => "E-33",
            -34 => "E-34",
            -35 => "E-35",
            -36 => "E-36",
            -37 => "E-37",
            -38 => "E-38",
            -39 => "E-39",

            -40 => "E-40",
            -41 => "E-41",
            -42 => "E-42",
            -43 => "E-43",
            -44 => "E-44",
            -45 => "E-45",
            -46 => "E-46",
            -47 => "E-47",
            -48 => "E-48",
            -49 => "E-49",

            -50 => "E-50",
            -51 => "E-51",
            -52 => "E-52",
            -53 => "E-53",
            -54 => "E-54",
            -55 => "E-55",
            -56 => "E-56",
            -57 => "E-57",
            -58 => "E-58",
            -59 => "E-59",

            -60 => "E-60",
            -61 => "E-61",
            -62 => "E-62",
            -63 => "E-63",
            -64 => "E-64",
            -65 => "E-65",
            -66 => "E-66",
            -67 => "E-67",
            -68 => "E-68",
            -69 => "E-69",

            -70 => "E-70",
            -71 => "E-71",
            -72 => "E-72",
            -73 => "E-73",
            -74 => "E-74",
            -75 => "E-75",
            -76 => "E-76",
            -77 => "E-77",
            -78 => "E-78",
            -79 => "E-79",

            -80 => "E-80",
            -81 => "E-81",
            -82 => "E-82",
            -83 => "E-83",
            -84 => "E-84",
            -85 => "E-85",
            -86 => "E-86",
            -87 => "E-87",
            -88 => "E-88",
            -89 => "E-89",

            -90 => "E-90",
            -91 => "E-91",
            -92 => "E-92",
            -93 => "E-93",
            -94 => "E-94",
            -95 => "E-95",
            -96 => "E-96",
            -97 => "E-97",
            -98 => "E-98",
            -99 => "E-99",

            -100 => "E-100",
            -101 => "E-101",
            -102 => "E-102",
            -103 => "E-103",
            -104 => "E-104",
            -105 => "E-105",
            -106 => "E-106",
            -107 => "E-107",
            -108 => "E-108",
            -109 => "E-109",

            -110 => "E-110",
            -111 => "E-111",
            -112 => "E-112",
            -113 => "E-113",
            -114 => "E-114",
            -115 => "E-115",
            -116 => "E-116",
            -117 => "E-117",
            -118 => "E-118",
            -119 => "E-119",

            -120 => "E-120",
            -121 => "E-121",
            -122 => "E-122",
            -123 => "E-123",
            -124 => "E-124",
            -125 => "E-125",
            -126 => "E-126",
            -127 => "E-127",
            -128 => "E-128",
        }
    }

    const fn lower_exp() -> &'static str {
        match const { EXP } {
            0 => "e0",
            1 => "e1",
            2 => "e2",
            3 => "e3",
            4 => "e4",
            5 => "e5",
            6 => "e6",
            7 => "e7",
            8 => "e8",
            9 => "e9",

            10 => "e10",
            11 => "e11",
            12 => "e12",
            13 => "e13",
            14 => "e14",
            15 => "e15",
            16 => "e16",
            17 => "e17",
            18 => "e18",
            19 => "e19",

            20 => "e20",
            21 => "e21",
            22 => "e22",
            23 => "e23",
            24 => "e24",
            25 => "e25",
            26 => "e26",
            27 => "e27",
            28 => "e28",
            29 => "e29",

            30 => "e30",
            31 => "e31",
            32 => "e32",
            33 => "e33",
            34 => "e34",
            35 => "e35",
            36 => "e36",
            37 => "e37",
            38 => "e38",
            39 => "e39",

            40 => "e40",
            41 => "e41",
            42 => "e42",
            43 => "e43",
            44 => "e44",
            45 => "e45",
            46 => "e46",
            47 => "e47",
            48 => "e48",
            49 => "e49",

            50 => "e50",
            51 => "e51",
            52 => "e52",
            53 => "e53",
            54 => "e54",
            55 => "e55",
            56 => "e56",
            57 => "e57",
            58 => "e58",
            59 => "e59",

            60 => "e60",
            61 => "e61",
            62 => "e62",
            63 => "e63",
            64 => "e64",
            65 => "e65",
            66 => "e66",
            67 => "e67",
            68 => "e68",
            69 => "e69",

            70 => "e70",
            71 => "e71",
            72 => "e72",
            73 => "e73",
            74 => "e74",
            75 => "e75",
            76 => "e76",
            77 => "e77",
            78 => "e78",
            79 => "e79",

            80 => "e80",
            81 => "e81",
            82 => "e82",
            83 => "e83",
            84 => "e84",
            85 => "e85",
            86 => "e86",
            87 => "e87",
            88 => "e88",
            89 => "e89",

            90 => "e90",
            91 => "e91",
            92 => "e92",
            93 => "e93",
            94 => "e94",
            95 => "e95",
            96 => "e96",
            97 => "e97",
            98 => "e98",
            99 => "e99",

            100 => "e100",
            101 => "e101",
            102 => "e102",
            103 => "e103",
            104 => "e104",
            105 => "e105",
            106 => "e106",
            107 => "e107",
            108 => "e108",
            109 => "e109",

            110 => "e110",
            111 => "e111",
            112 => "e112",
            113 => "e113",
            114 => "e114",
            115 => "e115",
            116 => "e116",
            117 => "e117",
            118 => "e118",
            119 => "e119",

            120 => "e120",
            121 => "e121",
            122 => "e122",
            123 => "e123",
            124 => "e124",
            125 => "e125",
            126 => "e126",
            127 => "e127",

            -1 => "e-1",
            -2 => "e-2",
            -3 => "e-3",
            -4 => "e-4",
            -5 => "e-5",
            -6 => "e-6",
            -7 => "e-7",
            -8 => "e-8",
            -9 => "e-9",

            -10 => "e-10",
            -11 => "e-11",
            -12 => "e-12",
            -13 => "e-13",
            -14 => "e-14",
            -15 => "e-15",
            -16 => "e-16",
            -17 => "e-17",
            -18 => "e-18",
            -19 => "e-19",

            -20 => "e-20",
            -21 => "e-21",
            -22 => "e-22",
            -23 => "e-23",
            -24 => "e-24",
            -25 => "e-25",
            -26 => "e-26",
            -27 => "e-27",
            -28 => "e-28",
            -29 => "e-29",

            -30 => "e-30",
            -31 => "e-31",
            -32 => "e-32",
            -33 => "e-33",
            -34 => "e-34",
            -35 => "e-35",
            -36 => "e-36",
            -37 => "e-37",
            -38 => "e-38",
            -39 => "e-39",

            -40 => "e-40",
            -41 => "e-41",
            -42 => "e-42",
            -43 => "e-43",
            -44 => "e-44",
            -45 => "e-45",
            -46 => "e-46",
            -47 => "e-47",
            -48 => "e-48",
            -49 => "e-49",

            -50 => "e-50",
            -51 => "e-51",
            -52 => "e-52",
            -53 => "e-53",
            -54 => "e-54",
            -55 => "e-55",
            -56 => "e-56",
            -57 => "e-57",
            -58 => "e-58",
            -59 => "e-59",

            -60 => "e-60",
            -61 => "e-61",
            -62 => "e-62",
            -63 => "e-63",
            -64 => "e-64",
            -65 => "e-65",
            -66 => "e-66",
            -67 => "e-67",
            -68 => "e-68",
            -69 => "e-69",

            -70 => "e-70",
            -71 => "e-71",
            -72 => "e-72",
            -73 => "e-73",
            -74 => "e-74",
            -75 => "e-75",
            -76 => "e-76",
            -77 => "e-77",
            -78 => "e-78",
            -79 => "e-79",

            -80 => "e-80",
            -81 => "e-81",
            -82 => "e-82",
            -83 => "e-83",
            -84 => "e-84",
            -85 => "e-85",
            -86 => "e-86",
            -87 => "e-87",
            -88 => "e-88",
            -89 => "e-89",

            -90 => "e-90",
            -91 => "e-91",
            -92 => "e-92",
            -93 => "e-93",
            -94 => "e-94",
            -95 => "e-95",
            -96 => "e-96",
            -97 => "e-97",
            -98 => "e-98",
            -99 => "e-99",

            -100 => "e-100",
            -101 => "e-101",
            -102 => "e-102",
            -103 => "e-103",
            -104 => "e-104",
            -105 => "e-105",
            -106 => "e-106",
            -107 => "e-107",
            -108 => "e-108",
            -109 => "e-109",

            -110 => "e-110",
            -111 => "e-111",
            -112 => "e-112",
            -113 => "e-113",
            -114 => "e-114",
            -115 => "e-115",
            -116 => "e-116",
            -117 => "e-117",
            -118 => "e-118",
            -119 => "e-119",

            -120 => "e-120",
            -121 => "e-121",
            -122 => "e-122",
            -123 => "e-123",
            -124 => "e-124",
            -125 => "e-125",
            -126 => "e-126",
            -127 => "e-127",
            -128 => "e-128",
        }
    }
}

/// Generic flag without explaination.
#[derive(PartialEq, Debug)]
pub struct ParseError;

/// Require [BaseCount::parse] to consume a string in full. The empty string is
/// rejected, and so is whitespace.
impl<const EXP: i8> std::str::FromStr for BaseCount<EXP> {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (c, read) = Self::parse(s.as_bytes());
        if read == 0 || read < s.len() {
            Err(ParseError)
        } else {
            Ok(c)
        }
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
        assert_eq!((0.into(), 2), Milli::parse(b".E"), "separators only");

        assert!("".parse::<Milli>().is_err(), "FromStr no text");
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
        let b0 = "18446744073709551615";
        assert_eq!(Ok(BaseCount::<0>::MAX), b0.parse());
        let b0l21 = "00000000000000000000018446744073709551615";
        assert_eq!(Ok(BaseCount::<0>::MAX), b0l21.parse());

        let f1 = "1844674407370955161.5";
        assert_eq!(Ok(BaseCount::<-1>::MAX), f1.parse());
        // …
        let f19 = "1.8446744073709551615";
        assert_eq!(Ok(BaseCount::<-19>::MAX), f19.parse());
        let f20 = "0.18446744073709551615";
        assert_eq!(Ok(BaseCount::<-20>::MAX), f20.parse());
        let f21 = "0.018446744073709551615";
        assert_eq!(Ok(BaseCount::<-21>::MAX), f21.parse());
        // …
        let f39 = "0.000000000000000000018446744073709551615";
        assert_eq!(Ok(BaseCount::<-39>::MAX), f39.parse());
        let f40 = "0.0000000000000000000018446744073709551615";
        assert_eq!(Ok(BaseCount::<-40>::MAX), f40.parse());
        let f41 = "0.00000000000000000000018446744073709551615";
        assert_eq!(Ok(BaseCount::<-41>::MAX), f41.parse());

        let b0e1 = "18446744073709551615e1";
        assert_eq!(Ok(BaseCount::<1>::MAX), b0e1.parse());
        let f1e2 = "1844674407370955161.5e2";
        assert_eq!(Ok(BaseCount::<1>::MAX), f1e2.parse());
        let f2e1 = "184467440737095516.15e1";
        assert_eq!(Ok(BaseCount::<-1>::MAX), f2e1.parse());
        let f41e22n = "0.00000000000000000000018446744073709551615e-22";
        assert_eq!(Ok(BaseCount::<-63>::MAX), f41e22n.parse());
        let f41e120 = "0.00000000000000000000018446744073709551615e120";
        assert_eq!(Ok(BaseCount::<79>::MAX), f41e120.parse());
    }

    #[test]
    fn parse_zero() {
        let in_nano_range = [
            "0", "00", "0.0", "00.0", "0.00", "00e00", "0.00e0", "00.00e-7",
        ];

        for s in in_nano_range {
            assert_eq!(Ok(Nano::ZERO), s.parse(), "parse {}", s);
        }

        // 21 non-significant digits
        assert_eq!(Ok(Kilo::ZERO), "000000000000000000000e3".parse());
        assert_eq!(Ok(Kilo::ZERO), "000000000000000000000e4".parse());
        assert_eq!(Ok(Milli::ZERO), "000000000000000000000".parse());
        assert_eq!(Ok(Nano::ZERO), "000000000000000000000e-9".parse());
        assert_eq!(Ok(Nano::ZERO), "000000000000000000000e-8".parse());

        // non-significant digits far out of range
        let hi_res = BaseCount::<-128>::ZERO;
        assert_eq!(Ok(hi_res), "0.0".parse());
        assert_eq!(Ok(hi_res), "00.00".parse());
        assert_eq!(Ok(hi_res), "000000000000000000000.0".parse());
        assert_eq!(Ok(hi_res), "0.000000000000000000000".parse());
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

// lookup table for decimal "00" up until "99"
const DOUBLE_DIGIT_TABLE: [u8; 200] = *b"\
    00010203040506070809\
    10111213141516171819\
    20212223242526272829\
    30313233343536373839\
    40414243444546474849\
    50515253545556575859\
    60616263646566676869\
    70717273747576777879\
    80818283848586878889\
    90919293949596979899";

fn fmt_int(f: &mut fmt::Formatter, n: u64) -> fmt::Result {
    // Buffer decimals for self.c with fixed positions. Thus the
    // least-significant digit is located at the last byte in buf.
    let mut buf = [MaybeUninit::<u8>::uninit(); 20];
    // Consume decimals from working copy until none left.
    let mut remain = n;

    // Set digits per two in buf with a lookup table.
    for pair_index in (0..10).rev() {
        let pair = (remain % 100) as usize;
        remain /= 100;

        buf[pair_index * 2 + 0].write(DOUBLE_DIGIT_TABLE[pair * 2 + 0]);
        buf[pair_index * 2 + 1].write(DOUBLE_DIGIT_TABLE[pair * 2 + 1]);

        if remain == 0 {
            let offset = if pair > 9 {
                pair_index * 2
            } else {
                pair_index * 2 + 1
            };
            // SAFETY: All bytes in buf since pair_index * 2 are set with ASCII
            // from the lookup table.
            return f.write_str(unsafe {
                from_utf8_unchecked(slice::from_raw_parts(
                    MaybeUninit::as_ptr(&buf[offset]),
                    20 - offset,
                ))
            });
        }
    }

    // SAFETY:: All bytes in buf are set with ASCII from the lookup table.
    f.write_str(unsafe {
        from_utf8_unchecked(slice::from_raw_parts(MaybeUninit::as_ptr(&buf[0]), 20))
    })
}

/// The highest number of fractions fixed to zero is `i8::MIN` minus 20 variable
/// digits for the `u64` count.
static MAX_ZERO_LEAD: &str = "0.000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";

/// Display the number in plain-decimal notation. Any EXP above zero causes E
/// notation (from `UpperExp`) instead.
///
/// Alternate formatting (with the "#" flag) displays the count of non-zero EXP
/// with a metric prefix and non-breaking space in between. EXP without prefix
/// definition get the count as a fraction of the next prefix in line, if any.
/// Otherwise, formatting falls back to E notation (for any EXP above 30).
///
/// ```
/// let small = b10::BaseCount::<-11>::from(72);
/// assert_eq!("0.72 n", format!("{small:#}"));
///
/// let large = b10::BaseCount::<8>::from(123456);
/// assert_eq!("12345.6 G", format!("{large:#}"));
/// ```
impl<const EXP: i8> fmt::Display for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            return self.fmt_metric_prefix(f);
        }
        if const { EXP == 0 } {
            return fmt_int(f, self.c);
        }
        if const { EXP > 0 } {
            // E notation for positive exponents
            return write!(f, "{self:E}");
        }
        assert!(const { EXP < 0 });

        // Buffer decimals for self.c with fixed positions. Thus the
        // least-significant digit is located at the last byte in buf.
        let mut buf: [u8; 20] = [b'0'; 20];
        // The leading-zero count equals the write index in buf.
        let mut lzc = buf.len();
        // Consume decimals from working copy until none left.
        let mut remain = self.c;

        // digits per two from least significant to most significant
        for pair_index in (0..10).rev() {
            let pair = (remain % 100) as usize;
            remain /= 100;

            buf[pair_index * 2 + 0] = DOUBLE_DIGIT_TABLE[pair * 2 + 0];
            buf[pair_index * 2 + 1] = DOUBLE_DIGIT_TABLE[pair * 2 + 1];

            if remain == 0 {
                if pair > 9 {
                    lzc = pair_index * 2 + 0;
                } else {
                    lzc = pair_index * 2 + 1;
                }
                break;
            }
        }

        // maybe fraction with leading zero guarantee
        if const { EXP <= -20 } {
            f.write_str(&MAX_ZERO_LEAD[..const { 2 - EXP as isize - 20 } as usize])?;

            // SAFETY: All buf's content lzc is set with bytes from the lookup table, which consists of valid ASCII exclusively.
            let digits = unsafe { from_utf8_unchecked(&buf) };
            return f.write_str(digits);
        }

        assert!(const { EXP > -20 && EXP < 0 });
        let frac_offset = const { 20 + EXP as isize } as usize;
        assert!(frac_offset > 0 && frac_offset < buf.len());

        // maybe integer part
        if lzc < frac_offset {
            let int = unsafe { from_utf8_unchecked(&buf[lzc..frac_offset]) };
            f.write_str(int)?;

            // with decimal separator
            buf[frac_offset - 1] = b'.';
            let frac = unsafe { from_utf8_unchecked(&buf[frac_offset - 1..]) };
            f.write_str(frac)
        } else if frac_offset == 1 {
            // write "0."
            f.write_str(&MAX_ZERO_LEAD[..2])?;
            let digits = unsafe { from_utf8_unchecked(&buf[frac_offset..]) };
            f.write_str(digits)
        } else {
            assert!(frac_offset >= 2);
            // set decimal separator
            buf[frac_offset - 1] = b'.';
            let s = unsafe { from_utf8_unchecked(&buf[frac_offset - 2..]) };
            f.write_str(s)
        }
    }
}

/// Print as `UpperExp`.
impl<const EXP: i8> fmt::Debug for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        return <BaseCount<EXP> as fmt::UpperExp>::fmt(self, f);
    }
}

/// Print the integer count with the base (fixed).
impl<const EXP: i8> fmt::LowerExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_int(f, self.c)?;
        f.write_str(BaseCount::<{ EXP }>::lower_exp())
    }
}

/// Print the integer count with the base (fixed).
impl<const EXP: i8> fmt::UpperExp for BaseCount<EXP> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_int(f, self.c)?;
        f.write_str(BaseCount::<{ EXP }>::upper_exp())
    }
}

#[cfg(test)]
mod fmt_tests {
    use super::*;

    #[test]
    fn least_significant_digit() {
        assert_eq!("1", format!("{}", BaseCount::<0>::from(1)));

        assert_eq!("2E1", format!("{}", BaseCount::<1>::from(2)));
        assert_eq!("3E2", format!("{}", BaseCount::<2>::from(3)));
        assert_eq!("7E19", format!("{}", BaseCount::<19>::from(7)));
        assert_eq!("8E20", format!("{}", BaseCount::<20>::from(8)));
        assert_eq!("9E21", format!("{}", BaseCount::<21>::from(9)));

        assert_eq!("0.2", format!("{}", BaseCount::<-1>::from(2)));
        assert_eq!("0.03", format!("{}", BaseCount::<-2>::from(3)));
        assert_eq!(
            "0.0000000000000000007",
            format!("{}", BaseCount::<-19>::from(7))
        );
        assert_eq!(
            "0.00000000000000000008",
            format!("{}", BaseCount::<-20>::from(8))
        );
        assert_eq!(
            "0.000000000000000000009",
            format!("{}", BaseCount::<-21>::from(9))
        );
    }

    #[test]
    #[rustfmt::skip]
    fn decimal_slide() {
        // 20 digits with trailing zero
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
        assert_eq!("0.042 q", format!("{:#}", BaseCount::<-33>::from(42)));
        assert_eq!("0.0042 q", format!("{:#}", BaseCount::<-34>::from(42)));
        assert_eq!("0.00042 q", format!("{:#}", BaseCount::<-35>::from(42)));
        // …
        assert_eq!("0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000042 q", format!("{:#}", BaseCount::<{ i8::MIN }>::from(42)));
    }

    #[test]
    fn exp() {
        let x = Milli::from(42);
        assert_eq!("42E-3", format!("{x:E}"), "upper case");
        assert_eq!("42e-3", format!("{x:e}"), "lower case");
        assert_eq!("42E-3", format!("{x:?}"), "from Debug");
    }

    #[test]
    fn all_zero() {
        let int = BaseCount::<0>::ZERO;
        assert_eq!("0", format!("{int}"));
        assert_eq!("0", format!("{int:#}"));
        assert_eq!("0e0", format!("{int:e}"));

        let max = BaseCount::<{ i8::MAX }>::ZERO;
        assert_eq!("0E127", format!("{max}"));
        assert_eq!("0E127", format!("{max:#}"));
        assert_eq!("0e127", format!("{max:e}"));

        let min = BaseCount::<{ i8::MIN }>::ZERO;
        assert_eq!(
            "0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            format!("{min}"),
        );
        assert_eq!(
            "0.00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 q",
            format!("{min:#}"),
        );
        assert_eq!("0e-128", format!("{min:e}"));

        let frac = BaseCount::<-5>::ZERO;
        assert_eq!("0.00000", format!("{frac}"));
        assert_eq!("0.00 m", format!("{frac:#}"));
        assert_eq!("0e-5", format!("{frac:e}"));
    }
}

/// Ascending increments with [BaseCount::ONE] until [BaseCount::MAX] is
/// reached.
///
/// ```
/// let mut asc = b10::Centi::ONE.asc();
/// assert_eq!(asc.next(), "0.02".parse().ok());
/// assert_eq!(asc.next(), "0.03".parse().ok());
///
/// assert_eq!(asc.min(), "0.04".parse().ok());
/// assert_eq!(asc.max(), Some(b10::Centi::MAX));
///
/// assert_eq!(asc.nth(5), "0.09".parse().ok());
/// assert_eq!(asc.next(), "0.10".parse().ok());
/// ```
#[derive(Clone, Copy)]
pub struct Ascending<const EXP: i8> {
    from: BaseCount<EXP>,
}

/// Descending decrements with [BaseCount::ONE] until [BaseCount::ZERO] is
/// reached.
///
/// ```
/// let mut desc = b10::Centi::from(12).desc();
/// assert_eq!(desc.next(), "0.11".parse().ok());
/// assert_eq!(desc.next(), "0.10".parse().ok());
///
/// assert_eq!(desc.min(), "0.00".parse().ok());
/// assert_eq!(desc.max(), "0.09".parse().ok());
///
/// assert_eq!(desc.nth(5), "0.04".parse().ok());
/// assert_eq!(desc.next(), "0.03".parse().ok());
/// ```
#[derive(Clone, Copy)]
pub struct Descending<const EXP: i8> {
    from: BaseCount<EXP>,
}

impl<const EXP: i8> Iterator for Ascending<EXP> {
    type Item = BaseCount<EXP>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.from.inc() {
            None => None,
            Some(inc) => {
                self.from = inc;
                Some(inc)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match usize::try_from(u64::MAX - self.from.c) {
            Err(_) => (usize::MAX, None),
            Ok(size) => (size, Some(size)),
        }
    }

    /// Count is not safe on systems with usize narrower than 64 bits.
    fn count(self) -> usize {
        // must panic on overflow if debug assertions are enabled
        (u64::MAX - self.from.c) as usize
    }

    fn last(self) -> Option<Self::Item> {
        if self.from == Self::Item::MAX {
            None
        } else {
            Some(Self::Item::MAX)
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        match self.from.c.checked_add(n as u64) {
            None => {
                self.from = Self::Item::MAX;
                None
            }
            Some(sum) => {
                self.from.c = sum;
                // n is zero based, so one more
                self.next()
            }
        }
    }

    fn max(self) -> Option<Self::Item> {
        self.last()
    }

    fn min(self) -> Option<Self::Item> {
        self.from.inc()
    }

    fn is_sorted(self) -> bool {
        true
    }
}

impl<const EXP: i8> Iterator for Descending<EXP> {
    type Item = BaseCount<EXP>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.from.dec() {
            None => None,
            Some(dec) => {
                self.from = dec;
                Some(dec)
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match usize::try_from(self.from.c) {
            Err(_) => (usize::MAX, None),
            Ok(size) => (size, Some(size)),
        }
    }

    /// Count is not safe on systems with usize narrower than 64 bits.
    fn count(self) -> usize {
        // must panic on overflow if debug assertions are enabled
        self.from.c as usize
    }

    fn last(self) -> Option<Self::Item> {
        if self.from == Self::Item::ZERO {
            None
        } else {
            Some(Self::Item::ZERO)
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        match self.from.c.checked_sub(n as u64) {
            None => {
                self.from = Self::Item::ZERO;
                None
            }
            Some(diff) => {
                self.from.c = diff;
                // n is zero based, so one more
                self.next()
            }
        }
    }

    fn max(self) -> Option<Self::Item> {
        self.from.dec()
    }

    fn min(self) -> Option<Self::Item> {
        self.last()
    }

    fn is_sorted(self) -> bool {
        false
    }
}

#[cfg(test)]
mod iterator_tests {
    use super::*;

    #[test]
    fn asc_halt() {
        let mut iter = Milli::from(u64::MAX - 2).asc();
        assert_eq!(iter.next(), Some(Milli::from(u64::MAX - 1)));
        assert_eq!(iter.next(), Some(Milli::from(u64::MAX - 0)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn desc_halt() {
        let mut iter = Kilo::from(2).desc();
        assert_eq!(iter.next(), Some(Kilo::ONE));
        assert_eq!(iter.next(), Some(Kilo::ZERO));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn asc_jumps() {
        let mut dozens = Natural::from(11).asc().step_by(12);
        assert_eq!(dozens.next(), "12".parse().ok());
        assert_eq!(dozens.next(), "24".parse().ok());
        assert_eq!(dozens.nth(9), "144".parse().ok());
    }

    #[test]
    fn desc_jumps() {
        let odd_countdown = Natural::from(10).desc().step_by(2);
        assert_eq!(
            odd_countdown.collect::<Vec<_>>(),
            vec![9.into(), 7.into(), 5.into(), 3.into(), 1.into()],
        );
    }
}

#[macro_use]
extern crate afl;
extern crate b10;

use b10::BaseCount;

fn main() {
    fuzz!(|data: &[u8]| {
        if data.len() < 16 {
            return;
        }
        let n1 = u64::from_ne_bytes(data[..8].try_into().unwrap());
        let n2 = u64::from_ne_bytes(data[8..16].try_into().unwrap());

        diff_fuzz::<{ i8::MIN }>(n1, n2);
        diff_fuzz::<{ i8::MIN }>(n2, n1);

        frac_fuzz::<{ i8::MIN }>(n1, n2);
        frac_fuzz::<{ i8::MIN }>(n2, n1);
    });
}

/// Difference must match sum again.
fn diff_fuzz<const EXP: i8>(a: u64, b: u64) {
    let minuend = BaseCount::<EXP>::from(a);
    let subtrahend = BaseCount::<EXP>::from(b);
    let (difference, neg) = minuend.sub(subtrahend);
    if neg {
        assert_eq!(
            difference.add(minuend),
            (subtrahend, false),
            "{minuend} − {subtrahend} = −{difference}",
        );
    } else {
        assert_eq!(
            difference.add(subtrahend),
            (minuend, false),
            "{minuend} − {subtrahend} = {difference}",
        );
    }
}

/// Quotient (with remainder) must match product again.
fn frac_fuzz<const EXP: i8>(a: u64, b: u64) {
    let divident = BaseCount::<EXP>::from(a);
    let divisor = BaseCount::<EXP>::from(b);
    match divident.div(divisor) {
        None => assert_eq!(divisor, BaseCount::<EXP>::ZERO),
        Some((quotient, remainder)) => {
            assert_ne!(divisor, BaseCount::<EXP>::ZERO);
            assert!(
                remainder < divisor,
                "{divident} ÷ {divisor} = {quotient} with {remainder}",
            );

            let (product, overflow): (BaseCount<EXP>, BaseCount<EXP>) =
                b10::Natural::from(quotient).mul(divisor);
            assert_eq!(
                overflow,
                BaseCount::<EXP>::ZERO,
                "{divident} ÷ {divisor} = {quotient} with {remainder}",
            );

            assert_eq!(
                product.add(remainder),
                (divident, false),
                "{divident} ÷ {divisor} = {quotient} with {remainder}; {quotient} × {divisor} = {product}",
            );
        }
    }
}

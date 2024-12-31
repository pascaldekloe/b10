#[macro_use]
extern crate afl;
extern crate b10;

fn main() {
    fuzz!(|data: &[u8]| {
        b10::Natural::parse(data);

        b10::Kilo::parse(data);
        b10::Milli::parse(data);

        b10::BaseCount::<{ i8::MIN }>::parse(data);
        b10::BaseCount::<{ i8::MAX }>::parse(data);
    });
}

fuzz: target/debug/parse-fuzz
	cargo +nightly afl fuzz -i seed -o run target/debug/parse-fuzz

target/debug/parse-fuzz: src/main.rs ../../src/lib.rs
	cargo +nightly afl build

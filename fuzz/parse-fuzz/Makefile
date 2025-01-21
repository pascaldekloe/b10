fuzz: target/debug/parse-fuzz
	cargo afl fuzz -i seed -o run target/debug/parse-fuzz

target/debug/parse-fuzz: src/main.rs ../../src/lib.rs
	cargo afl build

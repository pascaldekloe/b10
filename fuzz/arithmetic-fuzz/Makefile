fuzz:
	cargo afl build
	cargo afl fuzz -i seed -o run -g 16 -G 16 ../../target/debug/arithmetic-fuzz

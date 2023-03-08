all: bench

bench:
	RUST_BACKTRACE=full cargo bench --bench sha256_compression

test:
	RUST_BACKTRACE=full cargo test sha256_stark

example:
	# RUST_BACKTRACE=full cargo run --release --example time_sha256_compression
	RUST_BACKTRACE=full cargo run --release --example h3
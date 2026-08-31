CARGO ?= cargo
RUSTUP ?= rustup
LAKE ?= lake
WORKSPACE_FLAGS = --locked --release --workspace --all-targets --all-features
X86_64_RUSTFLAGS = -C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq,+sha,+aes

ifeq ($(shell uname -s),Darwin)
X86_64_TARGET ?= x86_64-apple-darwin
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_APPLE_DARWIN_RUSTFLAGS
else
X86_64_TARGET ?= x86_64-unknown-linux-gnu
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS
endif

.PHONY: test check format clippy clippy-x86 smoke-test formal-proof

test: check format clippy clippy-x86 smoke-test

check:
	$(CARGO) check $(WORKSPACE_FLAGS)

format:
	$(CARGO) fmt --all -- --check

clippy:
	$(CARGO) clippy $(WORKSPACE_FLAGS) -- -D warnings

clippy-x86:
	$(RUSTUP) target add $(X86_64_TARGET)
	$(X86_64_RUSTFLAGS_ENV)="$(X86_64_RUSTFLAGS)" \
		$(CARGO) clippy $(WORKSPACE_FLAGS) --target $(X86_64_TARGET) -- -D warnings

smoke-test:
	$(CARGO) test --locked --release -p flock-prover --features veil --lib r1cs_hashes::blake3_preimage::tests::succinct_veil_preimage_roundtrip_and_mutations -- --exact
	$(CARGO) test --locked --release -p flock-prover --features veil --lib r1cs_hashes::blake3_preimage::tests::succinct_veil_public_only_simulator_is_accepted -- --exact

formal-proof:
	LAKE="$(LAKE)" scripts/formal-proof.sh

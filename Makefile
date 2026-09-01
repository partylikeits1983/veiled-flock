CARGO ?= cargo
RUSTUP ?= rustup
LAKE ?= lake
WORKSPACE_FLAGS = --locked --release --workspace --all-targets --all-features
QUICKSTART_MESSAGES ?= messages.bin
QUICKSTART_PROOF ?= proof.bin
QUICKSTART_COUNT ?= 2
EXAMPLE_SAMPLES ?= 5
X86_64_RUSTFLAGS = -C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq,+sha,+aes

ifeq ($(shell uname -s),Darwin)
X86_64_TARGET ?= x86_64-apple-darwin
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_APPLE_DARWIN_RUSTFLAGS
else
X86_64_TARGET ?= x86_64-unknown-linux-gnu
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS
endif

.PHONY: test check format clippy clippy-x86 smoke-test formal-proof
.PHONY: quickstart quickstart-demo quickstart-messages quickstart-prove
.PHONY: quickstart-verify quickstart-roundtrip quickstart-clean
.PHONY: examples veil-examples preimage-scaling mle-eval-bench chain-bench
.PHONY: keccak-mid-density linear-sha-verifier keccak-chain-bench
.PHONY: gen-ligerito-configs native-hash-benches

test: check format clippy clippy-x86 smoke-test

quickstart: quickstart-demo quickstart-roundtrip

quickstart-demo:
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--bin veiled_flock -- demo

quickstart-messages:
	dd if=/dev/zero of="$(QUICKSTART_MESSAGES)" bs=64 count=$(QUICKSTART_COUNT)

quickstart-prove:
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--bin veiled_flock -- prove --message "$(QUICKSTART_MESSAGES)" \
		--out "$(QUICKSTART_PROOF)"

quickstart-verify:
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--bin veiled_flock -- verify --in "$(QUICKSTART_PROOF)"

quickstart-roundtrip: quickstart-messages
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--bin veiled_flock -- prove --message "$(QUICKSTART_MESSAGES)" \
		--out "$(QUICKSTART_PROOF)"
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--bin veiled_flock -- verify --in "$(QUICKSTART_PROOF)"

quickstart-clean:
	rm -f "$(QUICKSTART_MESSAGES)" "$(QUICKSTART_PROOF)"

examples: veil-examples preimage-scaling mle-eval-bench chain-bench
examples: keccak-mid-density linear-sha-verifier

veil-examples:
	$(CARGO) run --locked --release -p veil-examples --example mle_eval_zk
	$(CARGO) run --locked --release -p veil-examples --example zerocheck_zk
	$(CARGO) run --locked --release -p veil-examples --example root_zk

preimage-scaling:
	$(CARGO) run --locked --release -p flock-prover --features veil \
		--example preimage_scaling -- $(EXAMPLE_SAMPLES)

mle-eval-bench:
	$(CARGO) run --locked --release -p flock-prover --example mle_eval_bench

chain-bench:
	$(CARGO) run --locked --release -p flock-prover \
		--features unsound-challenger --example chain_bench

keccak-mid-density:
	$(CARGO) run --locked --release -p flock-prover --example keccak_mid_density

linear-sha-verifier:
	$(CARGO) run --locked --release -p flock-prover --example linear_sha_verifier

keccak-chain-bench:
	$(CARGO) run --locked --release -p flock-prover --example keccak_chain_bench

gen-ligerito-configs:
	$(CARGO) run --locked --release -p flock-prover --example gen_ligerito_configs

native-hash-benches:
	$(CARGO) bench --locked -p flock-prover --features veil --bench blake3_native_chain
	$(CARGO) bench --locked -p flock-prover --features veil --bench keccak_native_chain

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
	LAKE="$(LAKE)" $(CARGO) run --locked --release -p formal-proof -- verify

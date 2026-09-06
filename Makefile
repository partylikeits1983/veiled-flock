CARGO ?= cargo
RUSTUP ?= rustup
LAKE ?= lake
WORKSPACE_FLAGS = --locked --release --workspace --exclude flock-wasm-bench --all-targets --all-features
NATIVE_RUSTFLAGS = -C target-cpu=native
X86_64_RUSTFLAGS = -C target-cpu=x86-64-v3 -C target-feature=+pclmulqdq,+sha,+aes

ifeq ($(shell uname -s),Darwin)
X86_64_TARGET ?= x86_64-apple-darwin
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_APPLE_DARWIN_RUSTFLAGS
else
X86_64_TARGET ?= x86_64-unknown-linux-gnu
X86_64_RUSTFLAGS_ENV = CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS
endif

.PHONY: test check format clippy clippy-x86 no-std-check wasm-bench workspace-test formal-proof

test: check format clippy clippy-x86 no-std-check wasm-bench workspace-test

check:
	RUSTFLAGS="$(NATIVE_RUSTFLAGS)" $(CARGO) check $(WORKSPACE_FLAGS)

format:
	$(CARGO) fmt --all -- --check

clippy:
	RUSTFLAGS="$(NATIVE_RUSTFLAGS)" $(CARGO) clippy $(WORKSPACE_FLAGS) -- -D warnings

clippy-x86:
	$(RUSTUP) target add $(X86_64_TARGET)
	$(X86_64_RUSTFLAGS_ENV)="$(X86_64_RUSTFLAGS)" \
		$(CARGO) clippy $(WORKSPACE_FLAGS) --target $(X86_64_TARGET) -- -D warnings

no-std-check:
	$(CARGO) check --locked -p flock-core --no-default-features
	$(CARGO) check --locked -p veil-f128 --no-default-features
	$(CARGO) check --locked -p flock-prover --no-default-features

wasm-bench:
	$(RUSTUP) target add wasm32-unknown-unknown
	$(CARGO) build --locked --release -p flock-wasm-bench \
		--target wasm32-unknown-unknown

workspace-test:
	RUSTFLAGS="$(NATIVE_RUSTFLAGS)" $(CARGO) test $(WORKSPACE_FLAGS)

formal-proof:
	LAKE="$(LAKE)" $(CARGO) run --locked --release -p formal-proof -- verify

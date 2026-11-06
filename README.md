# Magma verification

Lean 4.36.0-rc2 project for checking RustCrypto Magma against `Magma/RFC8891.lean`.

## Build

```sh
./scripts/build.sh
```

The build installs Aeneas/Charon if needed, restores the SHA-256-verified
original RustCrypto `magma 0.10.0` crate, checks both Rust crates, runs
Charon/Aeneas, then runs `lake build` and `lake lint`.

## Layout

- `Magma/RFC8891.lean` — unchanged RFC specification.
- `rust/magma/` — ignored, pristine copy of the published RustCrypto crate;
  `setup-rustcrypto.sh` restores it at the start of every build.
- `rust/tc26/src/lib.rs` — **checked-in, editable Rust verification view**.
  This is the actual source passed to Charon for Tc26 encryption/decryption.
  It contains the original loop snippets and explanations of the three
  transformations: specialization, loop unrolling and the minimal I/O adapter.
- `rust/tc26/Cargo.toml` — independently checkable with Cargo and rust-analyzer.
  Its S-box module is imported directly from `rust/magma/src/sboxes.rs`.
- `Magma/RustCrypto/Code/` — generated Lean model of the original S-boxes.
- `Magma/RustCrypto/Tc26/` — generated Lean model of the Tc26 Rust crate.
- `Magma/Verification.lean` — imports both generated models and RFC 8891.

To inspect or validate the verification-side Rust crate:

```sh
./scripts/setup-rustcrypto.sh
cargo check --manifest-path rust/tc26/Cargo.toml --locked
cargo test --manifest-path rust/tc26/Cargo.toml --locked
```

There is no Python script generating Rust code. The checked-in
`rust/tc26/src/lib.rs` is the authoritative verification-side Rust input.

For Linux and other architectures, configure `AENEAS_ARCHIVE_URL` and
`AENEAS_ARCHIVE_SHA256` using a compatible archive from
[the Aeneas releases page](https://github.com/AeneasVerif/aeneas/releases).

## Verification boundary

The exact upstream `encrypt_block` and `decrypt_block` bodies are preserved
in `tools/magma-full.llbc`, but the original `cipher`/`hybrid-array`
interfaces are not translated by Aeneas. The checked-in Tc26 view keeps
their Feistel operations and byte packing, specializes `S::g` to `Tc26::g`,
expands the 32 rounds, and models `Block`/`InOut` with a small adapter.

Cargo tests compare the specialized view with the real RustCrypto Magma
on 256 deterministic key/block pairs and the RFC test vector. The generated
Lean files compile, but **formal proof of the adapter equivalence, the
source transformation, and equality to the RFC remains open**.

Generated Lean modules are excluded from lean-fmt.

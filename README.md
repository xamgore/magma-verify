# Magma verification

Lean 4.36.0-rc2 workspace for verifying RustCrypto Magma against `Magma/RFC8891.lean`.

## Build

```sh
./scripts/build.sh
```

The build restores the SHA-256-verified original RustCrypto `magma 0.10.0`,
checks the verification Rust source against the original methods, runs Cargo
checks/tests, extracts models using Charon/Aeneas, and runs `lake build` and
`lake lint`.

## Layout

- `Magma/RFC8891.lean` — unchanged RFC specification.
- `rust/magma/` — ignored, pristine upstream crate, restored on each build.
- `rust/tc26/src/lib.rs` — **checked-in Rust verification view**, readable
  in an IDE. Its encrypt/decrypt functions preserve the original RustCrypto
  `for` loops and Feistel operations.
- `rust/tc26/Cargo.toml` — separately checkable using Cargo/rust-analyzer.
  It imports the original S-box source directly from `rust/magma/src/sboxes.rs`.
- `scripts/check-tc26-source.py` — checks that both method bodies match
  upstream exactly after the two documented substitutions.
- `Magma/RustCrypto/Code/` — generated model of upstream S-boxes.
- `Magma/RustCrypto/Tc26/` — generated model of the Tc26-specialized
  methods, **with loops intact**.
- `Magma/Verification.lean` — imports both generated models and RFC 8891.

To inspect the Rust verification crate independently:

```sh
./scripts/setup-rustcrypto.sh
python3 scripts/check-tc26-source.py .
cargo check --manifest-path rust/tc26/Cargo.toml --locked
cargo test --manifest-path rust/tc26/Cargo.toml --locked
```

For other architectures, configure `AENEAS_ARCHIVE_URL` and
`AENEAS_ARCHIVE_SHA256` from the
[Aeneas releases](https://github.com/AeneasVerif/aeneas/releases).

## Verification boundary

The exact original RustCrypto `encrypt_block` and `decrypt_block` methods
remain in `tools/magma-full.llbc`. Their `cipher`/`hybrid-array` signatures
are not directly supported by the current Aeneas release.

The checked-in Tc26 view retains the original round loops, key indexing,
and block byte-packing logic. Only two changes are made to the method bodies:
`S::g` is specialized to `sboxes::Tc26::g`, and the verification-only
`InOut` adapter copies its eight-byte input before entering the loops.
The source checker fails if any other method-body change is detected.

Rust regression tests compare against upstream RustCrypto on 256
deterministic inputs and an RFC vector. The generated Lean modules compile,
but **formal equivalence of the adapter and a correctness theorem against
the RFC remain open**. No loops are unrolled.

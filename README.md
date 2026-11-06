# Magma verification

Lean 4.36.0-rc2 workspace for verifying RustCrypto Magma against `Magma/RFC8891.lean`.

## Build

```sh
./scripts/build.sh
```

The build restores the SHA-256-verified original RustCrypto `magma 0.10.0`,
checks the verification Rust source against the upstream methods, runs Cargo
tests, generates Lean using Charon/Aeneas, and runs `lake build` and
`lake lint`.

## Layout

- `Magma/RFC8891.lean` — unchanged RFC specification.
- `rust/magma/` — ignored, pristine upstream crate, restored on each build.
- `rust/tc26/src/lib.rs` — reviewable Tc26-specific Rust source. Its
  encryption/decryption methods preserve the original nested `for` loops,
  reverse iterations, key indexing, Feistel steps, and byte packing.
- `rust/tc26/src/adapter.rs` — **the only verification-side I/O shim**:
  a borrowed input/output pair over `[u8; 8]` with `get_in`/`get_out`.
  No `cipher` backend traits or `Block` types are reimplemented.
- `scripts/check-tc26-source.py` — rejects changes to the upstream round
  logic; only Tc26 specialization and the two I/O adaptations are permitted.
- `Magma/RustCrypto/Code/` — generated model of upstream S-boxes.
- `Magma/RustCrypto/Tc26/` — generated model of the Tc26 methods,
  **with loops intact**.
- `Magma/Verification.lean` — imports the RFC and generated models.

```sh
./scripts/setup-rustcrypto.sh
python3 scripts/check-tc26-source.py .
cargo check --manifest-path rust/tc26/Cargo.toml --locked
cargo test --manifest-path rust/tc26/Cargo.toml --locked
```

## Why a separate Tc26 model?

A tested two-line patch on the original RustCrypto `magma` crate replaces
`let b = block.get_in();` with `let b = block.get_in().0;`.
Cargo and Charon accept it, **but Aeneas still fails** on the
`hybrid-array::Array` / `ArraySize` / `AssocArraySize` type/trait cycle.

Using the actual `cipher::Block` in the Tc26 model also triggers that
cycle. The actual `cipher::InOut` can be extracted for the methods, but
Aeneas then requires opaque external Lean declarations for its type and
methods; the caller wrappers also fail to translate. Thus we retain one
small, explicit I/O adapter rather than introduce unproved external axioms.

The original `encrypt_block` and `decrypt_block` remain in
`tools/magma-full.llbc`. The checker enforces that the Tc26 model differs
in method signatures (`Block<Self>` to `[u8; 8]`), input copying, and
`S::g` specialization — **not in the cryptographic rounds**.

Rust tests compare 256 deterministic inputs and a known RFC vector against
unmodified RustCrypto. The generated Lean code type-checks, but **formal
equivalence of the adapter and correctness against RFC 8891 are still open**.

For other architectures, select a compatible binary archive from
[Aeneas releases](https://github.com/AeneasVerif/aeneas/releases) and set
`AENEAS_ARCHIVE_URL` / `AENEAS_ARCHIVE_SHA256`.

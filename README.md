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
- `Magma/RustCrypto/Correctness.lean` — table and arithmetic proofs.
- `Magma/RustCrypto/Rounds.lean` — generated Feistel loop-body steps.
- `Magma/RustCrypto/Keys.lean` — eight Rust words, all 32 RFC subkeys, and in-bounds array reads.
- `Magma/RustCrypto/Loops.lean` — termination and correctness of all eight
  generated inner-loop steps, conditional on Rust `g`.
- `Magma/Verification.lean` — imports the RFC, models, and proofs.

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
unmodified RustCrypto. In Lean, `Magma/RustCrypto/Correctness.lean` now proves:
all 128 Tc26 S-box entries match RFC 8891, Rust's 32-bit wrapping addition
and left rotation agree with the RFC operations, and the Aeneas model of the
adapter's input read satisfies its contract (using `step*`). It also proves
that RustCrypto's `g` agrees with RFC `g` **conditional on** the still-open
proof that the generated `apply_sbox` loop implements RFC `t`.
The generated **inner Feistel loop-body steps**, including both forward
and reverse decryption loops, are also proved equal to `Magma.G` when the
iterator, key lookup, and S-box premises are satisfied. The full
eight-step inner encryption loop is now proved to terminate and match
a pure sequence of RFC rounds, assuming correctness of Rust `g`.

**Open:** executable S-box loop correctness and proof that the
actual iterators execute the proved 32-key schedule, original `cipher` adapter equivalence, and the final theorem
`RustCryptoTc26.encrypt_with_words = Magma.encrypt` (with representations
converted). No theorem claiming full cipher correctness has been proved.

For other architectures, select a compatible binary archive from
[Aeneas releases](https://github.com/AeneasVerif/aeneas/releases) and set
`AENEAS_ARCHIVE_URL` / `AENEAS_ARCHIVE_SHA256`.

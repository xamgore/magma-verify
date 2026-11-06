# Magma verification

Lean 4.36.0-rc2 project comparing RustCrypto Magma with `Magma/RFC8891.lean`.

## Build

```sh
./scripts/build.sh
```

The script installs Aeneas/Charon, restores the SHA-256-checked original
RustCrypto `magma 0.10.0`, checks Rust tests, translates Rust to Lean,
then runs `lake build` and `lake lint`.

## Layout

- `Magma/RFC8891.lean` — unchanged formal specification.
- `Magma/RustCrypto/Code/` — Aeneas model of original S-boxes.
- `Magma/RustCrypto/Tc26/` — Aeneas model of the original encryption and
  decryption method bodies, specialized to Tc26 and mechanically unrolled.
- `Magma/Verification.lean` — imports both models alongside RFC 8891.
- `scripts/extract-tc26.py` — source extraction, specialization, loop expansion
  and a minimal verification-only `Block`/`InOut` adapter.
- `scripts/build.sh` — end-to-end reproducible pipeline.

`rust/magma/` is a managed, ignored extraction refreshed from the verified
archive on every build. No original source files are edited. Intermediate
artifacts live in ignored `tools/`.

For non-macOS platforms, configure `AENEAS_ARCHIVE_URL` and
`AENEAS_ARCHIVE_SHA256` using a compatible release from
[the Aeneas releases page](https://github.com/AeneasVerif/aeneas/releases).

## Verification boundary

The actual original `encrypt_block` and `decrypt_block` are also preserved in
`tools/magma-full.llbc`. Aeneas cannot translate their original
`cipher`/`hybrid-array` signatures directly.

The Tc26 model copies their original method bodies, specializes their
generic S-box calls, and **mechanically expands exactly 32 rounds** per
method. It uses a small separate `Block`/`InOut` adapter instead of the
original `cipher` library. Rust regression tests compare its result against
the unmodified RustCrypto Magma on 256 deterministic inputs and the RFC vector.

The resulting Lean models type-check, but **no formal equivalence theorem**
has yet been proved for the adapter, loop expansion, or RFC specification.

Generated Lean is excluded from `lean-fmt`.

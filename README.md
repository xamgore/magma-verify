# Magma verification (RustCrypto → Charon → Aeneas → Lean)

A single Lean/Lake project on **Lean 4.36.0-rc2** containing both
`Magma/RFC8891.lean` and the Aeneas-translated implementation model.

## Source and trust boundary

- `Magma/RFC8891.lean`: byte-identical copy of the specification from
  `~/Documents/magma`. The original repository is not modified.
- `rust/magma/`: **local verification fork** of RustCrypto `magma v0.10.0`
  (Cargo registry snapshot, Git SHA `c69a235c1289b8743aa66db6e6ed1bdfcf1e956d`).
  The initial import is in commit `dfd0140`.
- This fork has **one intentional implementation refactor**:
  `src/rounds.rs` contains both 32-round algorithms; production
  `BlockCipherEncBackend::encrypt_block` and
  `BlockCipherDecBackend::decrypt_block` call them.
  Charon/Aeneas can translate these core functions without importing the
  unsupported `cipher` / `hybrid-array` type graph.
- The loop schedule is written as bounded recursion because the pinned
  Aeneas release crashes during post-processing of the original nested loops.

This refactor is tested against RustCrypto's existing known-answer example,
but **has not yet been formally proved equivalent to the unmodified upstream
Rust implementation**. This matters for the overall verification claim.

## Tool versions

- Lean/Mathlib: `4.36.0-rc2`.
- Aeneas: `nightly-2026.11.06-4acbb6d`.
- Charon: `0.1.312` (`6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2`),
  bundled inside the macOS Aeneas release; **opam not needed**.
- Charon Rust: `nightly-2026-09-17`.
- `scripts/setup-tools.sh` verifies the release's SHA-256
  (`4e8ed96cf4f02478d1645c04d7f74ed1124913da588029a5743e85de8500e75c`).
- `scripts/prepare-aeneas-backend.sh` pins the Aeneas Lean backend to
  4.36 and reapplies two idempotent upstream API compatibility patches.
  The release's prebuilt Lean 4.35 artifacts are discarded, not reused.

## Regenerate and verify

```sh
cd ~/Documents/magma-verify
./scripts/regenerate.sh
lake build
lake exe fmt format --check
lake lint
(cd rust/magma && cargo test --locked)
```

`regenerate.sh` always runs Charon and Aeneas, overwrites only
`Generated/RustCrypto/Code/{Types,Funs}.lean`, and checks the output with
the **root** Lake project. It does **not** create or overwrite any Lake
configuration under `Generated/`. It extracts both `crate::rounds` and
`crate::sboxes`, including the RFC 8891 `Tc26` S-box.

Lean formatting matches `~/Documents/magma`: pinned `lean-fmt`,
100-column line width, no comment reflow, `Fmt.lean`, and the Lake
`fmt` lint driver. `Generated/**` is excluded from formatting
to preserve exact reproducibility of Aeneas output.

Rust source formatting is checked directly with
`rustfmt --edition 2024 --check src/lib.rs src/rounds.rs` from
`rust/magma`. The published Cargo manifest references a missing
`benches/mod.rs` in its registry snapshot, so `cargo fmt --all` fails
independently of the Rust source formatting.

## Current proof boundary

The actual Aeneas Lean output includes:

- `RustCrypto.rounds.encrypt_block_core` and `decrypt_block_core`;
- `RustCrypto.rounds.encrypt_schedule` and `decrypt_schedule`;
- `split_block`, `join_block`, the `g` transformation, and `Tc26` S-box.

**This is not a proof of RFC equivalence.** The generated recursions use
`partial_fixpoint`: their termination and the equality of the model to the
RFC spec are still proof obligations.

The external `cipher::InOut` adapters and `KeyInit` wrapper are also
not translated. Full-crate Aeneas translation still fails on
`hybrid-array` GAT/type-trait cycles; Charon `--opaque` and `--exclude`
experiments did not resolve it. A complete end-to-end proof must connect
those thin adapters to the verified core (or model the dependency graph),
and separately address the equivalence of this refactor to upstream RustCrypto.

The local `.lake/packages` is independent of the original project;
generated build caches and release binaries are excluded from Git.

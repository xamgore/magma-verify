# Magma / RustCrypto verification workspace

The target of verification is the **unmodified** RustCrypto `magma 0.10.0`
crate. Its published source is restored by `scripts/setup-rustcrypto.sh`,
not committed or patched in this repository.

## Reproduce

```sh
cd ~/Documents/magma-verify
./scripts/regenerate.sh
```

The script:
- fetches `magma-0.10.0.crate` from the local Cargo cache or crates.io,
  verifies SHA-256 `84fcdd6a71a6af65297be074d9d26cda7a2e98b86294ee0de0732b00c2063a61`,
  and refuses to use a modified source tree;
- checks original Rust code using `cargo fmt --all --check` and `cargo test --locked`;
- runs Charon with `--preset=aeneas` over the **entire original crate**,
  saving `tools/magma-full.llbc` (with the real `encrypt_block` and
  `decrypt_block` implementations);
- separately extracts `crate::sboxes` and generates Lean from it in
  `Generated/RustCrypto/Code/{Types,Funs}.lean`;
- builds the root Lean 4.36.0-rc2 Lake project and checks formatting.

`Magma/RFC8891.lean` remains a byte-identical copy from `~/Documents/magma`.
`Magma/Verification.lean` imports that specification and the generated S-box
model in the same Lean environment.

## Scope / open issue

Aeneas currently **does not** translate the original `encrypt_block` and
`decrypt_block` trait methods: the full `cipher`/`hybrid-array` dependency
graph triggers an internal error. The complete original functions *are* in
`magma-full.llbc`; that is not yet a verified Lean model.

Do not substitute a separately written round-core implementation.
The previous `rounds.rs` and its recursive replacement have been removed.
There is no claim of RFC functional equivalence yet.

## Toolchain / formatting

Aeneas `nightly-2026.11.06-4acbb6d` for macOS arm64 bundles Charon
`0.1.312` (commit `6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2`).
`scripts/setup-tools.sh` downloads and verifies the archive if missing.
`scripts/prepare-aeneas-backend.sh` adapts the Aeneas Lean backend to
Lean/Mathlib `4.36.0-rc2`.

Formatting matches `~/Documents/magma` (pinned `lean-fmt`, 100 columns,
`lake lint`). Generated Lean is deliberately excluded from formatting.

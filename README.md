# RustCrypto Magma — Aeneas/Lean verification workspace

Independent experiment; original repository at `~/Documents/magma` is untouched.

## Sources

- `Magma/RFC8891.lean`: byte-identical copy of the formal RFC 8891 spec
  from `~/Documents/magma/Magma/RFC8891.lean`.
- `rust/magma/`: RustCrypto `magma` v0.10.0 crate snapshot from local
  Cargo registry, upstream Git SHA `c69a235c1289b8743aa66db6e6ed1bdfcf1e956d`.
- `tools/aeneas/`: untracked Aeneas nightly archive, includes Charon.
- `Generated/RustCrypto/Code/`: actual Lean output from Aeneas.
- `scripts/regenerate.sh`: reproducible translation of S-box core.

## Toolchain

- Aeneas nightly `2026.11.06-4acbb6d` (macOS ARM64).
- Charon `0.1.312`, commit `6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2`.
- Charon Rust: `nightly-2026-09-17` (installed automatically).
- Root Lake project: Lean `4.36.0-rc2`, Mathlib `v4.36.0-rc2`.
- `Generated/` Lake project: Lean `4.35.0`, Mathlib `v4.35.0`.

The macOS Aeneas release is available at:
https://github.com/AeneasVerif/aeneas/releases/download/nightly-2026.11.06-4acbb6d/aeneas-macos-aarch64.tar.gz
SHA-256: `4e8ed96cf4f02478d1645c04d7f74ed1124913da588029a5743e85de8500e75c`.
The archive bundles `aeneas`, `charon`, `charon-driver`, and a prebuilt Lean backend.

## Commands

```sh
cd ~/Documents/magma-verify
lake build Magma                  # RFC 8891 — passes
cd rust/magma && cargo check --locked && cd ../..
./scripts/regenerate.sh           # Charon LLBC -> Aeneas Lean — passes
cd Generated && lake build RustCrypto
```

The root project currently reuses `~/Documents/magma/.lake/packages`
via an ignored symlink; regenerate dependencies via Lake for portability.

## Limitations

Full-crate Charon extraction succeeds (`rust/magma/magma.llbc`).
Full-crate Aeneas translation **fails** on mixed mutually recursive type/trait
declarations in the `hybrid-array` / `cipher` dependency graph.
Targeted extraction `--start-from=crate::sboxes` succeeds, producing
`Types.lean` and `Funs.lean` with `Tc26`, `gen_exp_sbox`,
`apply_sbox`, and `g`. Those modules build successfully.

Neither `Gost89::encrypt_block` nor `decrypt_block` is translated yet.
No implementation-vs-RFC correctness theorem has been proved.
Aeneas's Lean backend is on Lean 4.35, whereas this unchanged RFC formalization
requires Lean 4.36-rc2; unification of the toolchains remains necessary.

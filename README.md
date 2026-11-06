# Magma verification

Lean 4.36.0-rc2 project for checking the **unmodified** RustCrypto Magma implementation against `Magma/RFC8891.lean`.

## Build

```sh
./scripts/build.sh
```

The build installs the pinned Aeneas/Charon release, restores RustCrypto `magma 0.10.0` from a SHA-256-verified published archive, runs Rust formatting and tests, extracts LLBC, generates Lean for the original S-box computations, and runs `lake build` and `lake lint`.

`rust/magma/` is a **managed, ignored extraction**: each build replaces its contents with the verified release. Do not keep local edits there. The source archive is reused from Cargo's cache when available; downloads and extraction temporaries are deleted automatically. Build artifacts are kept in ignored `tools/`.

## Layout

- `Magma/RFC8891.lean` — unchanged formal specification.
- `Magma/RustCrypto/Code/` — generated Aeneas Lean source.
- `Magma/RustCrypto/README.md` — generated code and verification boundary.
- `Magma/Verification.lean` — imports the RFC and generated model.
- `scripts/setup-rustcrypto.sh` — restore the exact RustCrypto source.
- `scripts/setup-tools.sh` — install a compatible Aeneas/Charon release.
- `scripts/patch_aeneas_backend.py` — idempotent Lean 4.36 compatibility patches.
- `scripts/build.sh` — complete reproducible build.

For Linux or other platforms, select a suitable binary archive from [Aeneas releases](https://github.com/AeneasVerif/aeneas/releases), and configure `AENEAS_ARCHIVE_URL` and `AENEAS_ARCHIVE_SHA256` before running `build.sh`. The macOS ARM64 release is preconfigured. See `scripts/setup-tools.sh`.

## Verification status

The original `encrypt_block` and `decrypt_block` implementations are present in `tools/magma-full.llbc`, but Aeneas cannot yet translate their `cipher` / `hybrid-array` dependency graph. The original S-box code is translated and type-checked. **No functional-equivalence theorem has been proved.** We do not replace RustCrypto's encryption code with a verification-specific implementation.

The root project's `lean-fmt` configuration matches `~/Documents/magma`, excluding generated Lean files from reformatting.

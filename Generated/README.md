# Aeneas-generated RustCrypto S-box model

Generated from the **unchanged** RustCrypto Magma `src/sboxes.rs` using:

```sh
charon cargo --preset=aeneas --start-from=crate::sboxes --dest-file=magma-sboxes.llbc
aeneas -backend lean magma-sboxes.llbc -dest Generated -subdir /RustCrypto/Code -split-files -namespace RustCrypto
```

Run `../scripts/regenerate.sh` from the parent workspace for the actual
absolute paths and bundled binaries.

`RustCrypto/Code/Types.lean` and `Funs.lean` were produced by Aeneas.
This folder is also its own Lean 4.35 Lake project so that `lake build RustCrypto`
type-checks both generated modules against the bundled Aeneas backend.

The top-level RFC 8891 formalization remains a separate Lean 4.36-rc2
project. Full cipher encryption/decryption has **not** been translated.

# RustCrypto Magma — generated Lean

Aeneas generates `Code/Types.lean` and `Code/Funs.lean` directly from the original RustCrypto Magma S-box source. Do not edit these files manually.

Run `./scripts/build.sh` from the repository root. The output belongs to the root Lake library `Magma`; there is no second Lake project.

Charon also extracts the original `encrypt_block` and `decrypt_block` methods to `tools/magma-full.llbc`. Their full Aeneas translation remains blocked by the external `cipher` / `hybrid-array` type graph. This does **not** constitute a correctness proof.

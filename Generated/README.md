# Aeneas-generated original RustCrypto S-box model

`RustCrypto/Code/{Types,Funs}.lean` is generated from the **unmodified**
RustCrypto `magma 0.10.0` crate with `charon cargo --preset=aeneas
--start-from=crate::sboxes` and Aeneas.

Do not edit generated files. Run `../scripts/regenerate.sh` from this folder
or `./scripts/regenerate.sh` from the root.

The original `encrypt_block` / `decrypt_block` Rust methods are preserved
in `../tools/magma-full.llbc`, but they have **not** been translated
into Lean. No functional correctness theorem has been proved yet.

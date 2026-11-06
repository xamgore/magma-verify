# RustCrypto generated Lean

`Code/` is Aeneas output from original RustCrypto S-box functions.
`Tc26/` is Aeneas output from the checked-in verification Rust crate
`rust/tc26/src/lib.rs`. It specializes the original `encrypt_block` and
`decrypt_block` bodies to Tc26 and explicitly lists their 32 rounds.

Review or edit the verification Rust code directly in an IDE. Build it with:

```sh
cargo check --manifest-path rust/tc26/Cargo.toml --locked
```

Run `./scripts/build.sh` to regenerate Lean. Never edit generated files
manually.

The original trait methods remain in `tools/magma-full.llbc`. The
verification-side adapter and loop expansion are tested against RustCrypto,
but their equivalence is not formally proved.

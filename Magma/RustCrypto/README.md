# RustCrypto generated Lean

`Code/` is Aeneas output from the original RustCrypto S-boxes.
`Tc26/` is Aeneas output from `rust/tc26/src/lib.rs`.

The specialized `encrypt_block` and `decrypt_block` retain the original
nested `for` loops and `.rev()`, all subkey accesses, and Feistel steps.
Aeneas translates them into Lean loop definitions.

The only verification-side I/O shim lives in `rust/tc26/src/adapter.rs`;
it uses plain eight-byte arrays with input/output borrows, not a copied
implementation of `cipher`'s traits and `Block` type. The source checker
ensures the round algorithms still match the original RustCrypto.

Run `./scripts/build.sh` to regenerate and compile Lean. Do not edit
generated files manually. Formal adapter equivalence is still open.

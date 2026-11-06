# RustCrypto generated Lean

`Code/` contains the Aeneas translation of the original RustCrypto S-box
functions. `Tc26/` contains the generated Lean translation of the
checked-in verification Rust crate `rust/tc26/src/lib.rs`.

The encryption and decryption method bodies retain their original nested
`for` loops, `.rev()`, subkey indexing and Feistel expressions.
Aeneas translates them into explicit Lean loop definitions.

Only Tc26 specialization and copying the input from the simplified
`InOut` adapter are permitted changes to the method bodies. The script
`scripts/check-tc26-source.py` checks them against original RustCrypto.

Run `./scripts/build.sh` to regenerate Lean. Do not edit the generated
Lean files manually.

The simplified adapter is covered by Rust tests against the unmodified
upstream implementation; formal adapter equivalence is still to be proved.

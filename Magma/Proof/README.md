# RustCrypto Magma verification

The checked-in Aeneas output is exclusively `Magma/Rust/Types.lean` and
`Magma/Rust/Funs.lean`. It is regenerated from the pinned RustCrypto
`magma` crate using `rust/src/tc26.patch` and `rust/src/adapter.rs`.
Do not edit the generated files manually.

All handwritten Lean lives in `Magma/Proof/`:

- `Model.lean` specializes the extracted generic backend to the Tc26 S-box.
- `Common/` proves primitive arithmetic, key and round properties, and byte conversion.
- `Encrypt/` proves the encryption loops, round schedule, and block output.
- `Sbox/` proves expanded-table generation, substitution, and correspondence to RFC 8891.
- `Decrypt/` proves the decryption loops, key schedule, and block output.

`Magma/RFC8891.lean` provides the specification. `Magma/Verification.lean`
lists the theorem interfaces. The unconditional encryption and decryption
proofs are in `Sbox/Final.lean` and `Decrypt/Block.lean`; the conditional
block correspondence is developed in `Encrypt/Block.lean`.

The two Rust block method bodies are compared with the original archive
by `scripts/check-tc26-source.py`. The proof establishes correctness of
the translated, Tc26-specialized methods, not formal equivalence of the
safe I/O adapter with the external `cipher` API.

Run `./scripts/build.sh` to rebuild the model, typecheck the proofs,
run Lean formatting checks, and audit axioms.

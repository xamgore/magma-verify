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

`Correctness.lean` proves equality of all 128 original Tc26 table entries
with the RFC, the 32-bit arithmetic bridge, and the generated adapter's
input-read contract using Aeneas's `step*` tactic. The `g` correspondence
lemma explicitly assumes the unproved executable S-box loop specification.
`Rounds.lean` proves that generated encryption and decryption inner-loop
steps (including reverse traversal) compute exactly `Magma.G`, conditional
on the explicit iterator, key lookup, and substitution hypotheses. The full
the outer 24 forward rounds and final eight reverse rounds are now proved in `Outer.lean` and `Reverse.lean`. `Loops.lean` proves the
**entire eight-round generated encryption and initial decryption loops** under an explicit
Rust `g` correctness premise. `Keys.lean` verifies the
representation of all eight key words and the complete 32-key RFC schedule.

Run `./scripts/build.sh` to regenerate and compile Lean. Do not edit
generated files manually. Formal cipher adapter and full encryption
correctness remain open.


`Cipher.lean` also proves that the combined 32 rounds agree with
`Magma.encrypt` for all 256-bit keys and 64-bit blocks.

`Bytes.lean` proves that the Aeneas-generated `to_u32` conversion
succeeds on four-byte slices and matches big-endian BitVec conversion.

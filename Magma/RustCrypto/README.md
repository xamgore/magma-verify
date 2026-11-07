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

`Block.lean` proves byte-exact output for the full generated
`encrypt_block` and no panics or buffer errors, conditional on `Tc26::g`.
The specialized Rust source still needs separate equivalence justification
with the upstream trait dispatch and external adapter.

`Equivalence.lean` now proves byte-level `encrypt_with_words`
refinement to the RFC 8891 cipher for all keys/blocks, **assuming** the
generated `Tc26::g` implementation agrees with RFC `g`. The `native_decide`
shortcut was rejected because it introduces a separate native evaluator
trust axiom. The expanded S-box and substitution loops still need induction.

`SboxGeneration.lean` verifies the exact innermost body of the source-derived
`gen_exp_sbox` loop (including byte arithmetic and two-dimensional indexing)
under the explicit 4-bit-entry precondition. Its three nested loop
invariants and the `apply_sbox` iteration theorem remain open.

`SboxLoops.lean` closes all 4×16×16 original generator loop iterations;
`SboxTables.lean` connects their pure result to the concrete Tc26 instance.
`SboxApply.lean` proves an iteration of the original `apply_sbox` body is
in bounds and non-overflowing when preceding bytes satisfy the invariant.
The remaining proof obligations are exact expanded table lookups, the full
`apply_sbox` loop, and removal of the premise on `g`.

`SboxApplyLoops.lean` lifts the per-byte proof to the entire
four-iteration Aeneas-translated `apply_sbox` loop: all executions
terminate without out-of-bounds access or overflow. Byte-for-byte
equality of its output to `Magma.t` is still unproved.

`SboxApplyValue.lean` proves the **exact** result of one original
`apply_sbox` step; `SboxApplyValueLoop.lean` proves the full original
loop returns `tc26ApplyModel`. `SboxCell.lean`, `SboxOrdinal.lean`,
and `SboxPrefix.lean` prove every one of the 1024 expanded table
entries agrees with its two source S-box values.
Linking this to `Magma.t` for arbitrary input remains to be proved.

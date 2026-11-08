# RustCrypto Tc26 verification

`Tc26/` contains the Aeneas-generated model of the original RustCrypto
`magma` crate with the small patch from `rust/src/tc26.patch` applied.
The adapter is maintained in `rust/src/adapter.rs` and copied into the
fetched `rust/magma/src/` directory at build time. Generated Lean files
must not be edited manually.

The Rust `encrypt_block` and `decrypt_block` method bodies remain
unchanged, including their generic `S::g` dispatch, nested loops, key
accesses and byte packing. `scripts/check-tc26-source.py` checks this
against the unpatched archive source. `Tc26.lean` specializes the
extracted generic methods to the concrete Tc26 S-box.

## Lean proofs

- `Correctness.lean`: RustCrypto's original Tc26 S-box entries match
  RFC 8891; word addition and rotation agree with RFC operations;
  the earlier `g` bridge is available as a conditional lemma.
- `Rounds.lean`, `Keys.lean`, `Loops.lean`, `Outer.lean`,
  `Reverse.lean`, `Cipher.lean`: original loop bodies,
  iteration bounds and subkeys, and the full encryption Feistel
  schedule equivalent to RFC 8891.
- `Bytes.lean`, `Block.lean`, `Equivalence.lean`: original block
  byte representation and the complete encrypted output. The
  intermediate statements retain an explicit `g` premise.
- `SboxGeneration.lean`, `SboxLoops.lean`, `SboxTables.lean`:
  exact execution of all three original expanded-table loops.
- `SboxCell.lean`, `SboxOrdinal.lean`, `SboxPrefix.lean`:
  exact value of every generated expanded table entry.
- `SboxApply.lean`, `SboxApplyLoops.lean`,
  `SboxApplyValue.lean`, `SboxApplyValueLoop.lean`:
  safety, termination, and exact return value of the original
  four-iteration `apply_sbox` loop.
- `SboxRFC.lean`, `SboxMasks.lean`, `SboxNibbles.lean`,
  `SboxByte.lean`, `SboxPacking.lean`: exact RFC bit/nibble
  equivalence and full output-word assembly.
- SboxFinal.lean proves substitution, g, and block encryption without conditions.
- DecryptLoops.lean, DecryptCipher.lean, and DecryptBlock.lean prove all decryption
  loops, the RFC key schedule, and the exact plaintext byte output.

These are Lean proofs of the source-derived specialized Tc26 model,
not a new handwritten cipher implementation. They do not assert
formal equivalence of the I/O adapter to external `cipher` types:
that proof is intentionally out of scope. Both block methods are proved against RFC 8891.

Run `./scripts/build.sh` to regenerate the model, check the Rust source,
compile the Lean proofs, and check formatting.

# RustCrypto Tc26 verification

`Code/` is Aeneas output for the original RustCrypto Magma S-boxes.
`Tc26/` is Aeneas output for the checked Tc26-specialized source in
`rust/tc26/src/lib.rs`. Generated files must not be edited manually.

The specialized Rust `encrypt_block` and `decrypt_block` preserve
the original nested loops, reverse traversal, key accesses, Feistel
rounds, and byte packing. `scripts/check-tc26-source.py` rejects
unpermitted source changes. The verification-only I/O adapter lives
in `rust/tc26/src/adapter.rs`.

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

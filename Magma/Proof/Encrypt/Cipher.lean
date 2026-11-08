module

public import Magma.Proof.Encrypt.Reverse

@[expose] public section

/-!
# Full 32-round Feistel algorithm versus the RFC 8891 specification

The auxiliary round iterators are already connected to the Aeneas Rust
loops by theorems in Outer.lean and Reverse.lean. This theorem matches their
combined *pure result* to the RFC's Magma.encrypt for EVERY key and block.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.Proof

theorem encrypt_round_schedule_matches_rfc (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (l r : BitVec 32) :
    let out := runReverseRounds key 0 8 (repeat8Rounds key 3 (l, r))
    out.2 ++ out.1 = Magma.encrypt (rfcKeyOfWords key) (l ++ r) := by
  simp only [Magma.encrypt, Magma.E, Magma.GStar, Magma.concat]
  simp only [Magma.Internal.split, Magma.substring]
  simp only [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    round_key_matches_rust_schedule]
  simp [rustRoundKeyBV, Fin.foldl, runReverseRounds, repeat8Rounds, runKeyRounds, Magma.G,
    Magma.xor]

end Magma.Proof

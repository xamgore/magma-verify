module

public import Magma.Proof.Common.Rounds

@[expose] public section

/-!
# Master-key representation and 32-round key selection

These are the *representation* and key-selection lemmas. Full loop iterator
correctness is proved separately; this module does not assert that executing
the Rust methods satisfies the RFC.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

/-- Pure 8-word packing; the high-order word comes first. -/
def pack8Words (w : Fin 8 → BitVec 32) : BitVec 256 :=
  w 0 ++ w 1 ++ w 2 ++ w 3 ++ w 4 ++ w 5 ++ w 6 ++ w 7

lemma base_round_key_of_packed_words (w : Fin 8 → BitVec 32) (i : Fin 8) :
    Magma.baseRoundKey (pack8Words w) i = w i := by
  fin_cases i <;>
    ( simp only [Magma.baseRoundKey, Magma.substring, pack8Words]
      repeat (rw [BitVec.extractLsb'_append_eq_of_le (by decide)])
      first
      | rw [BitVec.extractLsb'_append_eq_right]
      | simp
      all_goals simp)

/-- Concatenate eight 32-bit words in high-to-low order to represent the RFC master key. -/
def rfcKeyOfWords (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) : BitVec 256 :=
  pack8Words (fun i => (key.val[i.val]!).bv)

lemma base_round_key_of_word_array (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (i : Fin 8) :
    Magma.baseRoundKey (rfcKeyOfWords key) i = (key.val[i.val]!).bv := by
  exact base_round_key_of_packed_words (fun i => (key.val[i.val]!).bv) i

/-- The first 24 rounds repeat the eight words; the final eight use them in reverse order. -/
def rustRoundKeyBV (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (r : Fin 32) : BitVec 32 :=
  if r.val < 24 then
    (key.val[r.val % 8]!).bv
  else
    (key.val[7 - r.val % 8]!).bv

theorem round_key_matches_rust_schedule (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (r : Fin 32) : Magma.roundKey (rfcKeyOfWords key) r = rustRoundKeyBV key r := by
  simp [Magma.roundKey, rustRoundKeyBV, base_round_key_of_word_array]

/-- Every in-bounds Rust key-array read succeeds. -/
lemma key_index_in_bounds
    (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (j : Std.Usize) (hj : j.val < 8) :
    Array.index_usize key j = ok (key.val[j.val]!) := by
  simp [Array.index_usize, hj, key.property]

end Magma.Proof

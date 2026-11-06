module

public import Magma.RustCrypto.Rounds

@[expose] public section

/-!
# 256-bit master key / eight RustCrypto words

These are the *representation* and key-selection lemmas. Full loop iterator
correctness is proved separately; this module does not assert that executing
the Rust methods satisfies the RFC.
-/

open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

/-- Pure 8-word packing; the high-order word comes first. -/
def pack8Words (w : Fin 8 → BitVec 32) : BitVec 256 :=
  w 0 ++ w 1 ++ w 2 ++ w 3 ++ w 4 ++ w 5 ++ w 6 ++ w 7

theorem pack8Words_round_key (w : Fin 8 → BitVec 32) (i : Fin 8) :
    Magma.baseRoundKey (pack8Words w) i = w i := by
  fin_cases i <;>
    ( simp only [Magma.baseRoundKey, Magma.substring, pack8Words]
      repeat (rw [BitVec.extractLsb'_append_eq_of_le (by decide)])
      first
      | rw [BitVec.extractLsb'_append_eq_right]
      | simp
      all_goals simp)

/-- The RFC 256-bit key represented by eight high-to-low RustCrypto words. -/
def rfcKeyOfWords (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) : BitVec 256 :=
  pack8Words (fun i => (key.val[i.val]!).bv)

theorem rfc_base_round_key_of_words (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (i : Fin 8) :
    Magma.baseRoundKey (rfcKeyOfWords key) i = (key.val[i.val]!).bv := by
  exact pack8Words_round_key (fun i => (key.val[i.val]!).bv) i

/-- RustCrypto's key scheduling expressed with the 8 machine words. -/
def rustRoundKeyBV (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (r : Fin 32) : BitVec 32 :=
  if r.val < 24 then
    (key.val[r.val % 8]!).bv
  else
    (key.val[7 - r.val % 8]!).bv

theorem rfc_round_key_of_words (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (r : Fin 32) :
    Magma.roundKey (rfcKeyOfWords key) r = rustRoundKeyBV key r := by
  simp [Magma.roundKey, rustRoundKeyBV, rfc_base_round_key_of_words]

/-- Every in-bounds Rust key-array read succeeds. -/
theorem rust_key_index_ok
    (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (j : Std.Usize) (hj : j.val < 8) :
    Array.index_usize key j = ok (key.val[j.val]!) := by
  simp [Array.index_usize, hj, key.property]

end Magma.RustCrypto

module

public import Magma.Proof.Sbox.RFC

@[expose] public section

/-!
# Kernel-checked byte and nibble extraction

Relates the original RustCrypto byte-mask-and-shift operation to
the RFC's four-bit slices for every arbitrary 32-bit input word.
Uses BitVec's verified bit rules, not native SAT reflection.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

private lemma mask255_bit (i : Nat) : ((255 : BitVec 32)).getLsbD i = decide (i < 8) := by
  change (BitVec.ofNat 32 (2 ^ 8 - 1)).getLsbD i = decide (i < 8)
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : i < 8 <;> simp [h] <;> omega

private lemma mask_byte_generic (a : BitVec 32) (s : Nat) (hs : s ≤ 24) :
    (a &&& ((255 : BitVec 32) <<< s)) >>> s = (BitVec.extractLsb' s 8 a).zeroExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
  have heq : s + i - s = i := by omega
  rw [heq, mask255_bit]
  by_cases h : i < 8
  · have h2 : s + i < 32 := by omega
    simp [hi, h, h2]
  · simp [hi, h]

lemma mask_byte_extract (a : BitVec 32) (r : Fin 4) :
    ((a &&& ((255 : BitVec 32) <<< (8 * r.val))) >>> (8 * r.val)) =
      (BitVec.extractLsb' (8 * r.val) 8 a).zeroExtend 32 := by
  exact mask_byte_generic a (8 * r.val) (by omega)

private lemma extract_nested_lo (a : BitVec 32) (s : Nat) :
    (a.extractLsb' s 8).extractLsb' 0 4 = a.extractLsb' s 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  simp [hi, show i < 8 by omega, show 4 + i < 8 by omega, Nat.add_assoc]

private lemma extract_nested_hi (a : BitVec 32) (s : Nat) :
    (a.extractLsb' s 8).extractLsb' 4 4 = a.extractLsb' (s + 4) 4 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  simp [hi, show i < 8 by omega, show 4 + i < 8 by omega, Nat.add_assoc]

lemma low_nibble_extract (a : BitVec 32) (r : Fin 4) :
    Magma.Internal.nibble a (loRow r) =
      BitVec.extractLsb' 0 4 (BitVec.extractLsb' (8 * r.val) 8 a) := by
  change a.extractLsb' (4 * (loRow r).val) 4 = _
  have hs : 4 * (loRow r).val = 8 * r.val := by
    simp only [loRow]
    omega
  rw [hs]
  exact (extract_nested_lo a (8 * r.val)).symm

lemma high_nibble_extract (a : BitVec 32) (r : Fin 4) :
    Magma.Internal.nibble a (hiRow r) =
      BitVec.extractLsb' 4 4 (BitVec.extractLsb' (8 * r.val) 8 a) := by
  change a.extractLsb' (4 * (hiRow r).val) 4 = _
  have hs : 4 * (hiRow r).val = 8 * r.val + 4 := by
    simp only [hiRow]
    omega
  rw [hs]
  exact (extract_nested_hi a (8 * r.val)).symm

end Magma.Proof

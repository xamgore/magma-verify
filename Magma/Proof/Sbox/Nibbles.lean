module

public import Magma.Proof.Sbox.Masks
public import Magma.Proof.Sbox.ApplyValueLoop

@[expose] public section

/-! # Four bytes and their RFC nibble positions

A symbolic 32-bit input is split into the exact byte used by the
RustCrypto `apply_sbox` body, then into its two RFC 4-bit components.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

def rUsize (r : Fin 4) : Std.Usize :=
  ⟨BitVec.ofNat _ r.val⟩

lemma row_index_usize_value (r : Fin 4) : (rUsize r).val = r.val := by
  unfold rUsize
  change r.val % (2 ^ System.Platform.numBits) = r.val
  rcases System.Platform.numBits_eq with h | h
  · simp only [h]
    omega
  · simp only [h]
    omega

lemma byteIndex_extract (a : Std.U32) (r : Fin 4) :
    byteIndex a (rUsize r) = (BitVec.extractLsb' (8 * r.val) 8 a.bv).toNat := by
  unfold byteIndex
  rw [row_index_usize_value, mask_byte_extract]
  exact BitVec.toNat_setWidth_of_le (by decide)

lemma byteIndex_nibbles (a : Std.U32) (r : Fin 4) :
    (Magma.Internal.nibble a.bv (loRow r)).toNat = byteIndex a (rUsize r) % 16 ∧
      (Magma.Internal.nibble a.bv (hiRow r)).toNat = byteIndex a (rUsize r) / 16 := by
  constructor
  · rw [low_nibble_extract, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, byteIndex_extract]
  · rw [high_nibble_extract, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, byteIndex_extract]
    have hsize : (BitVec.extractLsb' (8 * r.val) 8 a.bv).toNat < 256 :=
      (BitVec.extractLsb' (8 * r.val) 8 a.bv).isLt
    have hs : (BitVec.extractLsb' (8 * r.val) 8 a.bv).toNat / 16 < 16 := by omega
    simp only [show (2 ^ 4 : Nat) = 16 by decide, Nat.mod_eq_of_lt hs]

end Magma.Proof

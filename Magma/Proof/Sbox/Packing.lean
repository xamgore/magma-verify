module

public import Magma.Proof.Sbox.Byte

@[expose] public section

/-!
# Complete RFC substitution equality of original RustCrypto apply_sbox

All four original S-box bytes are concatenated in RFC order. Each byte
was already proved to be the pair of source-generated RFC nibbles.
The result is equal to `Magma.t` for all 2^32 words, not a test sample.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.Proof

def byteFor (a : Std.U32) (r : Fin 4) : BitVec 8 :=
  ((rustExpandedSbox.val[r.val]!).val[byteIndex a (rUsize r)]!).bv

private lemma packFourBytes (b0 b1 b2 b3 : BitVec 8) :
    (((b0.zeroExtend 32 <<< 0) + (b1.zeroExtend 32 <<< 8)) + (b2.zeroExtend 32 <<< 16)) +
        (b3.zeroExtend 32 <<< 24) =
      b3 ++ b2 ++ b1 ++ b0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_append_eq_mul_add]
  have h0 := b0.isLt
  have h1 := b1.isLt
  have h2 := b2.isLt
  have h3 := b3.isLt
  norm_num at *
  omega

private lemma next0 : expNextK 0#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expanded_sbox_inner_index_increments 0#usize (by decide))

private lemma next1 : expNextK 1#usize = 2#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expanded_sbox_inner_index_increments 1#usize (by decide))

private lemma next2 : expNextK 2#usize = 3#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expanded_sbox_inner_index_increments 2#usize (by decide))

private lemma rUsize_index (r : Fin 4) (n : Std.Usize) (h : n.val = r.val) : n = rUsize r :=
  UScalar.eq_of_val_eq (h.trans (row_index_usize_value r).symm)

private lemma rustSboxStep_at (a v : Std.U32) (r : Fin 4) :
    (rustSboxStep a (rUsize r) v).bv = v.bv + ((byteFor a r).zeroExtend 32 <<< (8 * r.val)) := by
  simp only [rustSboxStep, byteFor, UScalar.wrapping_add, UScalar.cast, UScalarTy.U32_numBits_eq,
    row_index_usize_value]

lemma rust_sbox_byte_packing_correct (a : Std.U32) :
    (rustSboxModel a).bv = (byteFor a 3 ++ byteFor a 2 ++ byteFor a 1 ++ byteFor a 0) := by
  unfold rustSboxModel
  simp only [rustSboxSteps]
  have h0 : (0#usize) = rUsize 0 := rUsize_index 0 0#usize (by decide)
  have h1 : (1#usize) = rUsize 1 := rUsize_index 1 1#usize (by decide)
  have h2 : (2#usize) = rUsize 2 := rUsize_index 2 2#usize (by decide)
  have h3 : (3#usize) = rUsize 3 := rUsize_index 3 3#usize (by decide)
  simp only [next0, next1, next2]
  rw [h0, h1, h2, h3]
  simp only [rustSboxStep_at]
  change
    (((0#32 + ((byteFor a 0).zeroExtend 32 <<< 0)) + ((byteFor a 1).zeroExtend 32 <<< 8)) +
          ((byteFor a 2).zeroExtend 32 <<< 16)) +
        ((byteFor a 3).zeroExtend 32 <<< 24) =
      (byteFor a 3 ++ byteFor a 2 ++ byteFor a 1 ++ byteFor a 0)
  simp only [show (0#32) = (0 : BitVec 32) by rfl, zero_add]
  exact packFourBytes (byteFor a 0) (byteFor a 1) (byteFor a 2) (byteFor a 3)

lemma sbox_byte_from_rfc_substitutions (a : Std.U32) (r : Fin 4) :
    byteFor a r =
      (Magma.π (hiRow r) (Magma.Internal.nibble a.bv (hiRow r))) ++
        (Magma.π (loRow r) (Magma.Internal.nibble a.bv (loRow r))) := by
  exact rust_byte_matches_rfc a r

theorem rust_model_matches_rfc (a : Std.U32) : (rustSboxModel a).bv = Magma.t a.bv := by
  rw [rust_sbox_byte_packing_correct]
  rw [sbox_byte_from_rfc_substitutions a 3, sbox_byte_from_rfc_substitutions a 2,
    sbox_byte_from_rfc_substitutions a 1, sbox_byte_from_rfc_substitutions a 0]
  simp only [Magma.t, loRow, hiRow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append_eq_mul_add]
  norm_num
  ring

end Magma.Proof

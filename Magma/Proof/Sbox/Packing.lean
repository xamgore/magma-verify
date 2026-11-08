module

public import Magma.Proof.Sbox.Byte

@[expose] public section

/-!
# Complete RFC substitution equality of original Tc26 apply_sbox

All four original S-box bytes are concatenated in RFC order. Each byte
was already proved to be the pair of source-generated RFC nibbles.
The result is equal to `Magma.t` for all 2^32 words, not a test sample.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.Proof

def byteFor (a : Std.U32) (r : Fin 4) : BitVec 8 :=
  ((tc26Expanded.val[r.val]!).val[byteIndex a (rUsize r)]!).bv

private theorem packFourBytes (b0 b1 b2 b3 : BitVec 8) :
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

private theorem next0 : expNextK 0#usize = 1#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expNextK_val 0#usize (by decide))

private theorem next1 : expNextK 1#usize = 2#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expNextK_val 1#usize (by decide))

private theorem next2 : expNextK 2#usize = 3#usize := by
  apply UScalar.eq_of_val_eq
  simpa using (expNextK_val 2#usize (by decide))

private theorem rUsize_index (r : Fin 4) (n : Std.Usize) (h : n.val = r.val) : n = rUsize r :=
  UScalar.eq_of_val_eq (h.trans (rUsize_val r).symm)

private theorem tc26Step_at (a v : Std.U32) (r : Fin 4) :
    (tc26Step a (rUsize r) v).bv = v.bv + ((byteFor a r).zeroExtend 32 <<< (8 * r.val)) := by
  simp only [tc26Step, byteFor, UScalar.wrapping_add, UScalar.cast, UScalarTy.U32_numBits_eq,
    rUsize_val]

theorem tc26_pure_packing (a : Std.U32) :
    (tc26ApplyModel a).bv = (byteFor a 3 ++ byteFor a 2 ++ byteFor a 1 ++ byteFor a 0) := by
  unfold tc26ApplyModel
  simp only [tc26Steps]
  have h0 : (0#usize) = rUsize 0 := rUsize_index 0 0#usize (by decide)
  have h1 : (1#usize) = rUsize 1 := rUsize_index 1 1#usize (by decide)
  have h2 : (2#usize) = rUsize 2 := rUsize_index 2 2#usize (by decide)
  have h3 : (3#usize) = rUsize 3 := rUsize_index 3 3#usize (by decide)
  simp only [next0, next1, next2]
  rw [h0, h1, h2, h3]
  simp only [tc26Step_at]
  change
    (((0#32 + ((byteFor a 0).zeroExtend 32 <<< 0)) + ((byteFor a 1).zeroExtend 32 <<< 8)) +
          ((byteFor a 2).zeroExtend 32 <<< 16)) +
        ((byteFor a 3).zeroExtend 32 <<< 24) =
      (byteFor a 3 ++ byteFor a 2 ++ byteFor a 1 ++ byteFor a 0)
  simp only [show (0#32) = (0 : BitVec 32) by rfl, zero_add]
  exact packFourBytes (byteFor a 0) (byteFor a 1) (byteFor a 2) (byteFor a 3)

theorem byteFor_rfc (a : Std.U32) (r : Fin 4) :
    byteFor a r =
      (Magma.π (hiRow r) (Magma.Internal.nibble a.bv (hiRow r))) ++
        (Magma.π (loRow r) (Magma.Internal.nibble a.bv (loRow r))) := by
  exact tc26_byte_matches_rfc a r

theorem tc26_model_matches_rfc (a : Std.U32) : (tc26ApplyModel a).bv = Magma.t a.bv := by
  rw [tc26_pure_packing]
  rw [byteFor_rfc a 3, byteFor_rfc a 2, byteFor_rfc a 1, byteFor_rfc a 0]
  simp only [Magma.t, loRow, hiRow]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append_eq_mul_add]
  norm_num
  ring

end Magma.Proof

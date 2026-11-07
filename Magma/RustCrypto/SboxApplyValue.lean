module

public import Magma.RustCrypto.SboxApplyLoops

@[expose] public section

/-!
# Exact original apply_sbox loop-body refinement

One original Aeneas-translated `apply_sbox` iteration reads the
corresponding input byte, indexes the expanded Tc26 table, shifts
the substituted byte into place, and adds it without overflow.
The `tc26Step` model is proved equal to the original body for
every bounded partial accumulator; it is not a replacement Rust body.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

def byteIndex (a : Std.U32) (i : Std.Usize) : Nat :=
  ((a.bv &&& ((255 : BitVec 32) <<< (8 * i.val))) >>> (8 * i.val)).toNat

def tc26Step (a : Std.U32) (i : Std.Usize) (v : Std.U32) : Std.U32 :=
  let x : Std.U8 := (tc26Expanded.val[i.val]!).val[byteIndex a i]!
  UScalar.wrapping_add v ⟨(UScalar.cast .U32 x).bv <<< (8 * i.val)⟩

private theorem byteExtractionBound (a : BitVec 32) (s : Nat) :
    ((a &&& ((255 : BitVec 32) <<< s)) >>> s).toNat < 256 := by
  let mask : BitVec 32 := (255 : BitVec 32) <<< s
  have hm : mask.toNat ≤ 255 * 2 ^ s := by
    simp only [mask, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ]
    exact Nat.mod_le _ _
  have hand : (a &&& mask).toNat ≤ mask.toNat := by
    simpa only [BitVec.toNat_and] using (Nat.and_le_right (n := a.toNat) (m := mask.toNat))
  have hp : 0 < 2 ^ s := pow_pos (by decide) _
  have hle : ((a &&& mask).toNat) / 2 ^ s ≤ 255 := by
    calc
      _ ≤ mask.toNat / 2 ^ s := Nat.div_le_div_right hand
      _ ≤ (255 * 2 ^ s) / (2 ^ s) := Nat.div_le_div_right hm
      _ = 255 := by simp
  simpa only [mask, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using
    (show ((a &&& mask).toNat) / 2 ^ s < 256 by omega)

private theorem shiftedU32Bound (b : Std.U32) (hb : b.val < 256) (s : Nat) :
    (b.bv <<< s).toNat ≤ 255 * 2 ^ s := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  calc
    (b.val * 2 ^ s) % (2 ^ 32) ≤ b.val * 2 ^ s := Nat.mod_le _ _
    _ ≤ 255 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)

private theorem castU8toU32_lt256 (b : Std.U8) : (UScalar.cast .U32 b).val < 256 := by
  have hb : b.val < 256 := by
    have h := UScalar.hBounds b
    simp only [UScalarTy.U8_numBits_eq] at h
    norm_num at h
    exact h
  rw [UScalar.cast_val_eq]
  have hc : b.val < 2 ^ UScalarTy.U32.numBits := by
    simp only [UScalarTy.U32_numBits_eq]
    norm_num
    omega
  simpa only [Nat.mod_eq_of_lt hc] using hb

private theorem byteStepSumBound (v b shifted : Std.U32) (n shift : Nat) (hv : v.val < 2 ^ (8 * n))
    (hb : b.val < 256) (hshift : shift = 8 * n) (hsh : shifted.bv = b.bv <<< shift) :
    v.val + shifted.val < 2 ^ (8 * (n + 1)) := by
  have hbound : shifted.val ≤ 255 * 2 ^ shift := by
    calc
      shifted.val = (b.bv <<< shift).toNat := congrArg BitVec.toNat hsh
      _ ≤ 255 * 2 ^ shift := shiftedU32Bound b hb shift
  rw [hshift] at hbound
  have hpow : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
    simp [Nat.mul_add, pow_add]
    ring
  rw [hpow]
  omega

/-- Exact result and overflow/bounds safety of an original RustCrypto S-box step. -/
theorem apply_sbox_step_value
    (a v : Std.U32)
    (iter : core.ops.range.Range Std.Usize)
    (hi : iter.start.val < iter.end.val)
    (hbound : iter.end.val ≤ 4)
    (hv : v.val < 2 ^ (8 * iter.start.val)) :
    RustCryptoTc26.sboxes.SboxExt.apply_sbox.default_loop.body tc26SboxExt a iter v
      ⦃ cf => ∃ it' v', cf = cont (it', v') ∧
        it'.start.val = iter.start.val + 1 ∧ it'.end = iter.end ∧
        v' = tc26Step a iter.start v ∧
        v'.val < 2 ^ (8 * it'.start.val) ⦄ := by
  unfold RustCryptoTc26.sboxes.SboxExt.apply_sbox.default_loop.body
  have hnext := rust_usize_range_next iter hi
  step with hnext
  subst o
  step*
  simp only [tc26_exp_sbox_correct, bind_ok]
  step*
  case hbound =>
    have hbits : i3.bv =
        (a.bv &&& ((255 : BitVec 32) <<< shift.val)) >>> shift.val := by
      calc
        i3.bv = i2.bv >>> shift.val := i3_post1
        _ = (a.bv &&& i1.bv) >>> shift.val :=
          congrArg (fun z : BitVec 32 => z >>> shift.val) i2_post1
        _ = (a.bv &&& ((255 : BitVec 32) <<< shift.val)) >>> shift.val :=
          congrArg (fun z : BitVec 32 => (a.bv &&& z) >>> shift.val) i1_post1
    have hbyte : i3.val < 256 := by
      change i3.bv.toNat < 256
      rw [hbits]
      exact byteExtractionBound a.bv shift.val
    have hk : k.val = i3.val := by
      rw [k_post, UScalar.cast_val_eq]
      have hsize : i3.val < 2 ^ UScalarTy.Usize.numBits := by
        simp only [UScalarTy.Usize_numBits_eq]
        rcases System.Platform.numBits_eq with h | h
        · rw [h]; norm_num; omega
        · rw [h]; norm_num; omega
      exact Nat.mod_eq_of_lt hsize
    have hlen : a2.length = 256 := by simp
    omega
  all_goals
    have hi5 : i5.val < 256 := by
      rw [i5_post]
      exact castU8toU32_lt256 i4
    have hsum : v.val + i6.val < 2^(8*(iter.start.val+1)) :=
      byteStepSumBound v i5 i6 iter.start.val shift.val
        hv hi5 shift_post i6_post1
  case hmax =>
    have hmax : 2^(8*(iter.start.val+1)) ≤ 2^32 := by
      gcongr
      omega
    rw [U32.max_eq]
    omega
  refine ⟨iter1, v1, rfl, o_post1, o_post2, ?_, ?_⟩
  · have hbits : i3.bv =
        (a.bv &&& ((255 : BitVec 32) <<< shift.val)) >>> shift.val := by
      calc
        i3.bv = i2.bv >>> shift.val := i3_post1
        _ = (a.bv &&& i1.bv) >>> shift.val :=
          congrArg (fun z : BitVec 32 => z >>> shift.val) i2_post1
        _ = (a.bv &&& ((255 : BitVec 32) <<< shift.val)) >>> shift.val :=
          congrArg (fun z : BitVec 32 => (a.bv &&& z) >>> shift.val) i1_post1
    have hbyte : i3.val < 256 := by
      change i3.bv.toNat < 256
      rw [hbits]
      exact byteExtractionBound a.bv shift.val
    have hidx : k.val = byteIndex a iter.start := by
      rw [k_post, UScalar.cast_val_eq]
      have hsize : i3.val < 2 ^ UScalarTy.Usize.numBits := by
        simp only [UScalarTy.Usize_numBits_eq]
        rcases System.Platform.numBits_eq with h | h
        · rw [h]; norm_num; omega
        · rw [h]; norm_num; omega
      rw [Nat.mod_eq_of_lt hsize]
      change i3.bv.toNat = _
      rw [hbits, shift_post]
      rfl
    have hrow : a2 = tc26Expanded.val[iter.start.val]! := by
      rw [a2_post]
      exact (getElem!_pos tc26Expanded.val iter.start.val
        (by simpa using (show iter.start.val < 4 by omega))).symm
    have hlookup : i4 =
        (tc26Expanded.val[iter.start.val]!).val[byteIndex a iter.start]! := by
      rw [i4_post, ← hrow, ← hidx]
      have hc : k.val < a2.val.length := by
        have hk : k.val < 256 := by
          rw [hidx]
          exact byteExtractionBound a.bv (8 * iter.start.val)
        simpa only [a2.property, show (256#usize).val = 256 by decide] using hk
      exact (getElem!_pos a2.val k.val hc).symm
    have hshifted : i6 = (⟨(UScalar.cast .U32
          ((tc26Expanded.val[iter.start.val]!).val[byteIndex a iter.start]!)).bv <<<
          (8 * iter.start.val)⟩ : Std.U32) := by
      apply UScalar.eq_of_val_eq
      apply congrArg BitVec.toNat
      calc
        i6.bv = i5.bv <<< shift.val := i6_post1
        _ = (UScalar.cast .U32 i4).bv <<< shift.val :=
          congrArg (fun z : Std.U32 => z.bv <<< shift.val) i5_post
        _ = (UScalar.cast .U32
            ((tc26Expanded.val[iter.start.val]!).val[byteIndex a iter.start]!)).bv <<< shift.val :=
          congrArg (fun z : Std.U8 => (UScalar.cast .U32 z).bv <<< shift.val) hlookup
        _ = (UScalar.cast .U32
            ((tc26Expanded.val[iter.start.val]!).val[byteIndex a iter.start]!)).bv <<<
            (8 * iter.start.val) := by rw [shift_post]
    have hno : v.val + i6.val < U32.size := by
      have hpow : 2 ^ (8 * (iter.start.val + 1)) ≤ 2 ^ 32 := by
        gcongr
        omega
      simp only [U32.size, U32.numBits, UScalarTy.U32_numBits_eq]
      omega
    have hwrap : v1 = UScalar.wrapping_add v i6 := by
      apply UScalar.eq_of_val_eq
      rw [v1_post, UScalar.wrapping_add_val_eq]
      simp only [UScalar.size_UScalarTyU32, Nat.mod_eq_of_lt hno]
    change v1 = UScalar.wrapping_add v (⟨(UScalar.cast .U32
      ((tc26Expanded.val[iter.start.val]!).val[byteIndex a iter.start]!)).bv <<<
      (8 * iter.start.val)⟩ : Std.U32)
    rw [← hshifted]
    exact hwrap
  · rw [v1_post, o_post1]
    exact hsum

end Magma.RustCrypto

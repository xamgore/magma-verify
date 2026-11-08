module

public import Magma.Proof.Sbox.Tables

@[expose] public section

/-!
# One original RustCrypto apply_sbox loop-body iteration

The source-derived loop body safely reads a byte of the input,
fetches its expanded S-box value, and updates the result without
arithmetic overflow or out-of-bounds reads. The bound on previously
completed bytes is explicit in the lemma statement.

The proof does not assume `apply_sbox = Magma.t`; that is still
a separate goal.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

private lemma byteExtractionBound (a : BitVec 32) (s : Nat) :
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

private lemma shiftedU32Bound (b : Std.U32) (hb : b.val < 256) (s : Nat) :
    (b.bv <<< s).toNat ≤ 255 * 2 ^ s := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  calc
    (b.val * 2 ^ s) % (2 ^ 32) ≤ b.val * 2 ^ s := Nat.mod_le _ _
    _ ≤ 255 * 2 ^ s := Nat.mul_le_mul_right _ (by omega)

private lemma castU8toU32_lt256 (b : Std.U8) : (UScalar.cast .U32 b).val < 256 := by
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

private lemma byteStepSumBound (v b shifted : Std.U32) (n shift : Nat) (hv : v.val < 2 ^ (8 * n))
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

/-- Correct and terminating one-step transition, with byte-bound preservation. -/
lemma apply_sbox_step_succeeds
    (a v : Std.U32)
    (iter : core.ops.range.Range Std.Usize)
    (hi : iter.start.val < iter.end.val)
    (hbound : iter.end.val ≤ 4)
    (hv : v.val < 2 ^ (8 * iter.start.val)) :
    Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop.body tc26SboxExt a iter v
      ⦃ cf => ∃ it' v', cf = cont (it', v') ∧
        it'.start.val = iter.start.val + 1 ∧ it'.end = iter.end ∧
        v'.val < 2 ^ (8 * it'.start.val) ⦄ := by
  unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop.body
  have hnext := usize_range_next_some iter hi
  step with hnext
  subst o
  step*
  simp only [tc26_expanded_sbox_constant_correct, bind_ok]
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
  refine ⟨iter1, v1, rfl, o_post1, o_post2, ?_⟩
  rw [v1_post, o_post1]
  exact hsum

end Magma.Proof

module

public import Magma.Proof.Encrypt.Equivalence

@[expose] public section

/-!
# Original RustCrypto `gen_exp_sbox` innermost loop body

These proofs use the source-derived Aeneas body, including checked arithmetic,
array bounds, and mutation. They prove each interior loop step for S-boxes
whose 4-bit entries are less than 16. They do **not** yet prove the three
nested loops terminate or the expanded table matches the RFC.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

private theorem inner_lookup_bound (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (row col : Std.Usize) (hr : row.val < 8) (hc : col.val < 16) (a : Std.Array Std.U8 16#usize)
    (v : Std.U8) (ha : a = sbox.val[row.val]'(by simpa using hr))
    (hv : v = a.val[col.val]'(by simpa using hc))
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16, ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    v.val < 16 := by
  have hsmall := hvals ⟨row.val, hr⟩ ⟨col.val, hc⟩
  have hrow : row.val < sbox.val.length := by simpa using hr
  have hcol : col.val < a.val.length := by simpa using hc
  rw [getElem!_pos sbox.val row.val hrow] at hsmall
  rw [getElem!_pos (sbox.val[row.val]'hrow).val col.val (by simpa [ha] using hcol)] at hsmall
  simpa [ha, hv] using hsmall

private theorem u8_shl4 (x : Std.U8) (hx : x.val < 16) : (x.bv <<< 4).toNat = x.val * 16 := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (x.val * 16) % 256 = x.val * 16
  omega

private theorem usize_shl4 (x : Std.Usize) (hx : x.val < 16) : (x.bv <<< 4).toNat = x.val * 16 := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (x.val * 16) % (2 ^ System.Platform.numBits) = x.val * 16
  rcases System.Platform.numBits_eq with h | h
  · simp only [h]
    omega
  · simp only [h]
    omega

def expWrite (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (i j k : Std.Usize) :
    Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  let t0 := ((sbox.val[2 * i.val]!).val[j.val]!)
  let t1 := ((sbox.val[2 * i.val + 1]!).val[k.val]!)
  let v : Std.U8 := ⟨t0.bv + (t1.bv <<< 4)⟩
  let c : Std.Usize := ⟨BitVec.ofNat _ (j.val + k.val * 16)⟩
  out.set i ((out.val[i.val]!).set c v)

def expNextK (k : Std.Usize) : Std.Usize :=
  UScalar.wrapping_add k 1#usize

/-- A successful original inner-loop step writes the expanded Tc26 entry,
    increments k, and has no overflow or bounds failure. -/
theorem gen_exp_inner_step
    (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize)
    (i j k : Std.Usize)
    (hi : i.val < 4) (hj : j.val < 16) (hk : k.val < 16)
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16,
        ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    Magma.Rust.sboxes.gen_exp_sbox_loop0_loop0_loop0.body sbox i j out k
      ⦃ cf => cf = cont (expWrite sbox out i j k, expNextK k) ⦄ := by
  unfold Magma.Rust.sboxes.gen_exp_sbox_loop0_loop0_loop0.body
  step*
  case hmax =>
    have hi1 : i1.val < 8 := by omega
    have hi3 : i3.val < 8 := by omega
    have hs2 : i2.val < 16 :=
      inner_lookup_bound sbox i1 j hi1 hj a i2 a_post i2_post hvals
    have hs4 : i4.val < 16 :=
      inner_lookup_bound sbox i3 k hi3 hk a1 i4 a1_post i4_post hvals
    have hshift : i5.val = i4.val * 16 := by
      calc
        i5.val = i5.bv.toNat := rfl
        _ = (i4.bv <<< 4).toNat := congrArg BitVec.toNat i5_post1
        _ = i4.val * 16 := u8_shl4 i4 hs4
    rw [U8.max_eq]
    omega
  case hy =>
    rcases System.Platform.numBits_eq with h | h
    · simp [h]
    · simp [h]
  case hmax =>
    have hshift : i6.val = k.val * 16 :=
      (congrArg BitVec.toNat i6_post1).trans (usize_shl4 k hk)
    have hmaxU : 255 ≤ Usize.max := by
      rcases Usize.bounds_eq with h | h
      · rw [h, U32.max_eq]; omega
      · rw [h, U64.max_eq]; omega
    omega
  case hbound =>
    have hshift : i6.val = k.val * 16 :=
      (congrArg BitVec.toNat i6_post1).trans (usize_shl4 k hk)
    have hlen : a2.length = 256 := by simp
    omega
  have hk1 : k1 = expNextK k := by
    apply UScalar.eq_of_val_eq
    rw [k1_post]
    simp only [expNextK, UScalar.wrapping_add_val_eq]
    have hsize : k.val + 1 < UScalar.size .Usize := by
      simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
      rcases System.Platform.numBits_eq with h | h
      · rw [h]
        norm_num
        omega
      · rw [h]
        norm_num
        omega
    simp only [show (1#usize).val = 1 by rfl, Nat.mod_eq_of_lt hsize]
  rw [hk1]
  congr 2
  rw [index_mut_back_post, a3_post]
  unfold expWrite
  have hi2 : i.val < out.val.length := by simpa using hi
  have ha2 : a2 = out.val[i.val]! := by
    rw [a2_post]
    exact (getElem!_pos out.val i.val hi2).symm
  have hrow0 : 2*i.val < sbox.val.length := by simp; omega
  have hrow1 : 2*i.val+1 < sbox.val.length := by simp; omega
  have hcol0 : j.val < a.val.length := by simpa using hj
  have hcol1 : k.val < a1.val.length := by simpa using hk
  have hrowA : sbox.val[2*i.val]! = a := by
    calc
      sbox.val[2*i.val]! = sbox.val[i1.val]! :=
        congrArg (fun n => sbox.val[n]!) i1_post.symm
      _ = a := (getElem!_pos sbox.val i1.val
        (by omega)).trans a_post.symm
  have hrowB : sbox.val[2*i.val+1]! = a1 := by
    have hidx : i3.val = 2*i.val+1 := by omega
    calc
      sbox.val[2*i.val+1]! = sbox.val[i3.val]! :=
        congrArg (fun n => sbox.val[n]!) hidx.symm
      _ = a1 := (getElem!_pos sbox.val i3.val
        (by omega)).trans a1_post.symm
  have ht0 : (sbox.val[2*i.val]!).val[j.val]! = i2 := by
    rw [hrowA, getElem!_pos a.val j.val hcol0]
    exact i2_post.symm
  have ht1 : (sbox.val[2*i.val+1]!).val[k.val]! = i4 := by
    rw [hrowB, getElem!_pos a1.val k.val hcol1]
    exact i4_post.symm
  have hvalC : c.val = j.val + k.val*16 := by
    rw [c_post]
    congr 1
    exact (congrArg BitVec.toNat i6_post1).trans (usize_shl4 k hk)
  have hc : c.bv = BitVec.ofNat _ (j.val + k.val*16) := by
    rw [← hvalC]
    exact (Usize.BitVec_ofNat_val c).symm
  have hv : v.bv = i2.bv + (i4.bv <<< 4) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, ← i5_post1]
    have hwidth : i2.val + i5.val < 256 := by
      rw [← v_post]
      exact v.bv.isLt
    change v.val = (i2.val + i5.val) % 256
    rw [Nat.mod_eq_of_lt hwidth]
    exact v_post
  rw [ha2, ht0, ht1]
  apply congrArg (out.set i)
  apply congrArg₂ (Std.Array.set (out.val[i.val]!) )
  · apply UScalar.eq_of_val_eq
    have hh : j.val + k.val*16 < 2 ^ System.Platform.numBits := by
      rcases System.Platform.numBits_eq with h | h
      · rw [h]; norm_num; omega
      · rw [h]; norm_num; omega
    change c.val = (j.val + k.val*16) % (2 ^ System.Platform.numBits)
    rw [Nat.mod_eq_of_lt hh]
    exact hvalC
  · apply UScalar.eq_of_val_eq
    change v.bv.toNat = (i2.bv + (i4.bv <<< 4)).toNat
    exact congrArg BitVec.toNat hv

end Magma.Proof

module

public import Magma.Proof.Sbox.Ordinal

@[expose] public section

/-!
# All 1024 generated Tc26 S-box entries, proved pointwise

Induction over each of the original three nested loops shows exactly
which logical output cells are written and proves the final expanded
table's full contents for every row and byte.
This proof does not evaluate or unroll any Rust loop or use native_decide.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result

namespace Magma.Proof

def writeTime (i j k : Std.Usize) : Nat :=
  i.val * 256 + j.val * 16 + k.val

theorem writeTime_next (i j k : Std.Usize) (hk : k.val < 16) :
    writeTime i j (expNextK k) = writeTime i j k + 1 := by
  simp only [writeTime, expNextK_val k hk]
  omega

theorem expFillK_pointwise (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i j : Std.Usize)
    (hi : i.val < 4) (hj : j.val < 16) (n : Nat) :
    ∀ (k : Std.Usize) (out : ExpTable),
      k.val + n ≤ 16 →
        ∀ (r : Fin 4) (c : Fin 256),
          expCell (expFillK sbox i j n k out) r c =
            if writeTime i j k ≤ writeOrdinal r c ∧ writeOrdinal r c < writeTime i j k + n then
              expectedExpByte sbox r c
            else expCell out r c := by
  induction n with
  | zero =>
    intro k out hk r c
    simp [expFillK]
  | succ n ih =>
    intro k out hk r c
    have hlt : k.val < 16 := by omega
    have hnext : (expNextK k).val + n ≤ 16 := by
      rw [expNextK_val k hlt]
      omega
    have hind := ih (expNextK k) (expWrite sbox out i j k) hnext r c
    simp only [expFillK]
    rw [hind, writeTime_next i j k hlt, expWrite_pointwise sbox out i j k hi hj hlt r c]
    simp only [writeTime]
    let st : Nat := i.val * 256 + j.val * 16 + k.val
    let x : Nat := writeOrdinal r c
    change
      (if st + 1 ≤ x ∧ x < st + 1 + n then expectedExpByte sbox r c
        else if x = st then expectedExpByte sbox r c else expCell out r c) =
        if st ≤ x ∧ x < st + (n + 1) then expectedExpByte sbox r c else expCell out r c
    by_cases hA : st + 1 ≤ x ∧ x < st + 1 + n
    · have hB : st ≤ x ∧ x < st + (n + 1) := by omega
      simp only [ite_eq_left hA, ite_eq_left hB]
    · by_cases hC : x = st
      · have hB : st ≤ x ∧ x < st + (n + 1) := by omega
        simp only [ite_eq_right hA, ite_eq_left hC, ite_eq_left hB]
      · have hB : ¬(st ≤ x ∧ x < st + (n + 1)) := by omega
        simp only [ite_eq_right hA, ite_eq_right hC, ite_eq_right hB]

private theorem extendInterval (p step n x : Nat) (yes no : α) :
    (if p + step ≤ x ∧ x < p + step + step * n then yes
      else if p ≤ x ∧ x < p + step then yes else no) =
      if p ≤ x ∧ x < p + step * (n + 1) then yes else no := by
  have hmul : step * (n + 1) = step * n + step := Nat.mul_succ _ _
  by_cases hA : p + step ≤ x ∧ x < p + step + step * n
  · have hB : p ≤ x ∧ x < p + step * (n + 1) := by
      rw [hmul]
      omega
    simp only [ite_eq_left hA, ite_eq_left hB]
  · by_cases hC : p ≤ x ∧ x < p + step
    · have hB : p ≤ x ∧ x < p + step * (n + 1) := by
        rw [hmul]
        omega
      simp only [ite_eq_right hA, ite_eq_left hC, ite_eq_left hB]
    · have hB : ¬(p ≤ x ∧ x < p + step * (n + 1)) := by
        rw [hmul]
        omega
      simp only [ite_eq_right hA, ite_eq_right hC, ite_eq_right hB]

def jStart (i j : Std.Usize) : Nat :=
  i.val * 256 + j.val * 16

private theorem jStart_next (i j : Std.Usize) (hj : j.val < 16) :
    jStart i (expNextK j) = jStart i j + 16 := by
  simp only [jStart, expNextK_val j hj]
  omega

private theorem expFillK16_pointwise (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (i j : Std.Usize) (hi : i.val < 4) (hj : j.val < 16) (out : ExpTable) (r : Fin 4)
    (c : Fin 256) :
    expCell (expFillK sbox i j 16 0#usize out) r c =
      if jStart i j ≤ writeOrdinal r c ∧ writeOrdinal r c < jStart i j + 16 then
        expectedExpByte sbox r c
      else expCell out r c := by
  have h := expFillK_pointwise sbox i j hi hj 16 0#usize out (by decide) r c
  simp only [writeTime, jStart, show (0#usize).val = 0 by rfl, Nat.add_zero] at h ⊢
  exact h

theorem expFillJ_pointwise (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i : Std.Usize)
    (hi : i.val < 4) (n : Nat) :
    ∀ (j : Std.Usize) (out : ExpTable),
      j.val + n ≤ 16 →
        ∀ (r : Fin 4) (c : Fin 256),
          expCell (expFillJ sbox i n j out) r c =
            if jStart i j ≤ writeOrdinal r c ∧ writeOrdinal r c < jStart i j + 16 * n then
              expectedExpByte sbox r c
            else expCell out r c := by
  induction n with
  | zero =>
    intro j out hj r c
    simp [expFillJ]
  | succ n ih =>
    intro j out hj r c
    have hlt : j.val < 16 := by omega
    have hnext : (expNextK j).val + n ≤ 16 := by
      rw [expNextK_val j hlt]
      omega
    have hind := ih (expNextK j) (expFillK sbox i j 16 0#usize out) hnext r c
    simp only [expFillJ]
    rw [hind, jStart_next i j hlt, expFillK16_pointwise sbox i j hi hlt out r c]
    exact
      extendInterval (jStart i j) 16 n (writeOrdinal r c) (expectedExpByte sbox r c)
        (expCell out r c)

def iStart (i : Std.Usize) : Nat :=
  i.val * 256

private theorem iStart_next (i : Std.Usize) (hi : i.val < 4) :
    iStart (expNextK i) = iStart i + 256 := by
  simp only [iStart, expNextK_val i (by omega)]
  omega

private theorem expFillJ16_pointwise (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (i : Std.Usize) (hi : i.val < 4) (out : ExpTable) (r : Fin 4) (c : Fin 256) :
    expCell (expFillJ sbox i 16 0#usize out) r c =
      if iStart i ≤ writeOrdinal r c ∧ writeOrdinal r c < iStart i + 256 then
        expectedExpByte sbox r c
      else expCell out r c := by
  have h := expFillJ_pointwise sbox i hi 16 0#usize out (by decide) r c
  simp only [jStart, iStart, show (0#usize).val = 0 by rfl, Nat.zero_mul, Nat.add_zero] at h ⊢
  norm_num at h ⊢
  exact h

theorem expFillI_pointwise (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (n : Nat) :
    ∀ (i : Std.Usize) (out : ExpTable),
      i.val + n ≤ 4 →
        ∀ (r : Fin 4) (c : Fin 256),
          expCell (expFillI sbox n i out) r c =
            if iStart i ≤ writeOrdinal r c ∧ writeOrdinal r c < iStart i + 256 * n then
              expectedExpByte sbox r c
            else expCell out r c := by
  induction n with
  | zero =>
    intro i out hi r c
    simp [expFillI]
  | succ n ih =>
    intro i out hi r c
    have hlt : i.val < 4 := by omega
    have hnext : (expNextK i).val + n ≤ 4 := by
      rw [expNextK_val i (by omega)]
      omega
    have hind := ih (expNextK i) (expFillJ sbox i 16 0#usize out) hnext r c
    simp only [expFillI]
    rw [hind, iStart_next i hlt, expFillJ16_pointwise sbox i hlt out r c]
    exact
      extendInterval (iStart i) 256 n (writeOrdinal r c) (expectedExpByte sbox r c)
        (expCell out r c)

theorem tc26Expanded_cell (r : Fin 4) (c : Fin 256) :
    expCell tc26Expanded r c = expectedExpByte tc26Table r c := by
  have h :=
    expFillI_pointwise tc26Table 4 0#usize
      (Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u8)) (by decide) r c
  have hbound : writeOrdinal r c < 1024 := by
    unfold writeOrdinal
    have hm : c.val % 16 < 16 := Nat.mod_lt _ (by decide)
    have hq : c.val / 16 < 16 := by omega
    omega
  simp only [iStart, show (0#usize).val = 0 by rfl, Nat.zero_mul, Nat.zero_le, true_and,
    show 256 * 4 = 1024 by decide] at h
  simp [hbound] at h
  exact h

end Magma.Proof

module

public import Magma.Proof.Sbox.Cell

@[expose] public section

/-!
# Injective write address for the original expansion loops

The generated body writes row `i`, column `j + 16*k`.
The address `256*i + 16*j + k` is injective on the prescribed ranges,
and each write changes exactly that one output byte.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

def expSourceByte (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i j k : Std.Usize) :
    Std.U8 :=
  let lo := (sbox.val[2 * i.val]!).val[j.val]!
  let hi := (sbox.val[2 * i.val + 1]!).val[k.val]!
  ⟨lo.bv + (hi.bv <<< 4)⟩

def expectedExpByte (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (r : Fin 4)
    (c : Fin 256) : Std.U8 :=
  let lo := (sbox.val[2 * r.val]!).val[c.val % 16]!
  let hi := (sbox.val[2 * r.val + 1]!).val[c.val / 16]!
  ⟨lo.bv + (hi.bv <<< 4)⟩

def writeOrdinal (r : Fin 4) (c : Fin 256) : Nat :=
  r.val * 256 + (c.val % 16) * 16 + c.val / 16

private theorem colBound (j k : Std.Usize) (hj : j.val < 16) (hk : k.val < 16) :
    j.val + k.val * 16 < 256 := by omega

private theorem usizeIndex (j k : Std.Usize) (hj : j.val < 16) (hk : k.val < 16) :
    (⟨BitVec.ofNat _ (j.val + k.val * 16)⟩ : Std.Usize).val = j.val + k.val * 16 := by
  change (j.val + k.val * 16) % (2 ^ System.Platform.numBits) = j.val + k.val * 16
  rcases System.Platform.numBits_eq with h | h
  · simp only [h]
    omega
  · simp only [h]
    omega

private theorem expectedExpByte_source (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (i j k : Std.Usize) (_hi : i.val < 4) (hj : j.val < 16) (_hk : k.val < 16) (r : Fin 4)
    (c : Fin 256) (hr : r.val = i.val) (hc : c.val = j.val + k.val * 16) :
    expectedExpByte sbox r c = expSourceByte sbox i j k := by
  have hmod : (j.val + k.val * 16) % 16 = j.val := by omega
  have hdiv : (j.val + k.val * 16) / 16 = k.val := by omega
  simp only [expectedExpByte, expSourceByte, hr, hc, hmod, hdiv]

theorem writeOrdinal_eq (r : Fin 4) (c : Fin 256) (i j k : Std.Usize) (hi : i.val < 4)
    (hj : j.val < 16) (hk : k.val < 16) :
    writeOrdinal r c = i.val * 256 + j.val * 16 + k.val ↔
      r.val = i.val ∧ c.val = j.val + k.val * 16 := by
  have hmod : c.val % 16 < 16 := Nat.mod_lt _ (by decide)
  have hdiv : c.val / 16 < 16 := by omega
  have hdecomp : c.val % 16 + 16 * (c.val / 16) = c.val := Nat.mod_add_div _ _
  have hsuffix : (c.val % 16) * 16 + c.val / 16 < 256 := by omega
  simp only [writeOrdinal]
  constructor
  · intro heq
    have hrow : r.val = i.val := by omega
    have hsub : (c.val % 16) * 16 + c.val / 16 = j.val * 16 + k.val := by omega
    have hq : c.val / 16 = k.val := by omega
    have hm : c.val % 16 = j.val := by omega
    exact ⟨hrow, by omega⟩
  · rintro ⟨hr, hc⟩
    omega

/-- Exact functional write at one unique ordinal, all other bytes unchanged. -/
theorem expWrite_pointwise
    (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : ExpTable) (i j k : Std.Usize)
    (hi : i.val < 4) (hj : j.val < 16) (hk : k.val < 16)
    (r : Fin 4) (c : Fin 256) :
    expCell (expWrite sbox out i j k) r c =
      if writeOrdinal r c = i.val * 256 + j.val * 16 + k.val then
        expectedExpByte sbox r c else expCell out r c := by
  have hsrc := expectedExpByte_source sbox i j k hi hj hk r c
  have hord := writeOrdinal_eq r c i j k hi hj hk
  unfold expWrite
  change expCell (writeCell out i
    (⟨BitVec.ofNat _ (j.val + k.val * 16)⟩ : Std.Usize)
    (expSourceByte sbox i j k)) r c = _
  rw [writeCell_pointwise]
  rw [usizeIndex j k hj hk]
  by_cases hcell : writeOrdinal r c = i.val * 256 + j.val * 16 + k.val
  · have h := hord.mp hcell
    simp only [hcell, h.1.symm, h.2.symm, and_self, ↓reduceIte]
    exact (hsrc h.1 h.2).symm
  · have h : ¬(i.val = r.val ∧ j.val + k.val * 16 = c.val) := by
      intro hh
      exact hcell (hord.mpr ⟨hh.1.symm,hh.2.symm⟩)
    simp only [hcell, h, ↓reduceIte]

end Magma.Proof

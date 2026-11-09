module

public import Magma.Proof.Sbox.Tables

@[expose] public section

/-!
# Each expanded table cell contains its two expected 4-bit substitutions

Elementary functional lemma for the Aeneas two-dimensional array type,
with both in-bounds and outside-cell cases.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

abbrev ExpTable :=
  Std.Array (Std.Array Std.U8 256#usize) 4#usize

def expCell (out : ExpTable) (r : Fin 4) (c : Fin 256) : Std.U8 :=
  (out.val[r.val]!).val[c.val]!

def writeCell (out : ExpTable) (row col : Std.Usize) (v : Std.U8) : ExpTable :=
  out.set row ((out.val[row.val]!).set col v)

/-- One write changes only the selected row/column. -/
lemma writeCell_pointwise (out : ExpTable) (row col : Std.Usize)
    (v : Std.U8) (r : Fin 4) (c : Fin 256) :
    expCell (writeCell out row col v) r c =
      if row.val = r.val ∧ col.val = c.val then v else expCell out r c := by
  unfold expCell writeCell
  by_cases hr : row.val = r.val
  · have hrow : ((out.set row ((out.val[row.val]!).set col v)).val[r.val]!) =
        (out.val[row.val]!).set col v := by
      simpa only [Array.getElem!_Nat_eq] using
        (Array.getElem!_Nat_set_eq out row r.val
          ((out.val[row.val]!).set col v)
          ⟨hr, by simpa using r.isLt⟩)
    rw [hrow]
    by_cases hc : col.val = c.val
    · have hcol : (((out.val[row.val]!).set col v).val[c.val]!) = v := by
        simpa only [Array.getElem!_Nat_eq] using
          (Array.getElem!_Nat_set_eq (out.val[row.val]!) col c.val v
            ⟨hc, by simpa using c.isLt⟩)
      rw [hcol]
      simp [hr, hc]
    · have hcol : (((out.val[row.val]!).set col v).val[c.val]!) =
          (out.val[row.val]!).val[c.val]! := by
        simpa only [Array.getElem!_Nat_eq] using
          (Array.getElem!_Nat_set_ne (out.val[row.val]!) col c.val v hc)
      rw [hcol]
      simp [hr, hc]
  · have hrow : ((out.set row ((out.val[row.val]!).set col v)).val[r.val]!) =
        out.val[r.val]! := by
      simpa only [Array.getElem!_Nat_eq] using
        (Array.getElem!_Nat_set_ne out row r.val ((out.val[row.val]!).set col v) hr)
    rw [hrow]
    simp [hr]

end Magma.Proof

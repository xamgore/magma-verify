module

public import Magma.RustCrypto.SboxLoops

@[expose] public section

/-!
# Concrete Tc26 S-box expansion

The generated three nested loops produce the exact pure table
`tc26Expanded`. Every one of the 128 4-bit source entries is bounded by 15.
This module does **not** yet assert that each expanded output entry agrees
with the RFC's nibble substitution.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

theorem tc26_values_lt16 (i : Fin 8) (j : Fin 16) :
    ((tc26Table.val[i.val]!).val[j.val]!).val < 16 := by
  fin_cases i <;> fin_cases j <;>
    ( unfold tc26Table RustCryptoTc26.sboxes.Tc26.Insts.MagmaSboxesSbox.SBOX
      decide)

def tc26ExpandedSpec : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  Std.Array.from
    (List.ofFn fun (i : Fin 4) =>
      Std.Array.from
        (List.ofFn fun (c : Fin 256) =>
          let lo := (tc26Table.val[2 * i.val]!).val[c.val % 16]!
          let hi := (tc26Table.val[2 * i.val + 1]!).val[c.val / 16]!
          (⟨lo.bv + (hi.bv <<< 4)⟩ : Std.U8))
        (by
          simp only [List.length_ofFn]; decide))
    (by
      simp only [List.length_ofFn]; decide)

private def outZero : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u8)

def tc26Expanded : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  expFillI tc26Table 4 0#usize outZero

private theorem result_eq_ok_of_spec {α : Type} (p : Result α) (x : α) (h : p ⦃ out => out = x ⦄) :
    p = ok x := by
  induction p using Result.cases with
  | ret v =>
    have hv : v = x := by simpa only [WP.spec_ok] using h
    simp [hv]
  | vis e k => exact False.elim ((WP.spec_vis ..).mp h)
  | div => exact False.elim ((WP.spec_div).mp h)

theorem tc26_gen_exp_correct : RustCryptoTc26.sboxes.gen_exp_sbox tc26Table = ok tc26Expanded := by
  exact result_eq_ok_of_spec _ _ (gen_exp_sbox_full tc26Table tc26_values_lt16)

theorem tc26_exp_sbox_correct : tc26SboxExt.EXP_SBOX = ok tc26Expanded := by
  change
    (do
        let a ← ok tc26Table;
        RustCryptoTc26.sboxes.gen_exp_sbox a) =
      ok tc26Expanded
  simpa only [bind_ok] using tc26_gen_exp_correct

end Magma.RustCrypto

module

public import Magma.Proof.Sbox.Loops

@[expose] public section

/-!
# Concrete RustCrypto S-box expansion

The generated three nested loops produce the exact pure table
`rustExpandedSbox`. Every one of the 128 4-bit source entries is bounded by 15.
This module does **not** yet assert that each expanded output entry agrees
with the RFC's nibble substitution.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

lemma rust_sbox_entries_lt16 (i : Fin 8) (j : Fin 16) :
    ((rustSboxTable.val[i.val]!).val[j.val]!).val < 16 := by
  fin_cases i <;> fin_cases j <;>
    ( unfold rustSboxTable Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox.SBOX
      decide)

def rustExpandedSboxSpec : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  Std.Array.from
    (List.ofFn fun (i : Fin 4) =>
      Std.Array.from
        (List.ofFn fun (c : Fin 256) =>
          let lo := (rustSboxTable.val[2 * i.val]!).val[c.val % 16]!
          let hi := (rustSboxTable.val[2 * i.val + 1]!).val[c.val / 16]!
          (⟨lo.bv + (hi.bv <<< 4)⟩ : Std.U8))
        (by
          simp only [List.length_ofFn]; decide))
    (by
      simp only [List.length_ofFn]; decide)

private def outZero : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u8)

def rustExpandedSbox : Std.Array (Std.Array Std.U8 256#usize) 4#usize :=
  expFillI rustSboxTable 4 0#usize outZero

private lemma result_eq_ok_of_spec {α : Type} (p : Result α) (x : α) (h : p ⦃ out => out = x ⦄) :
    p = ok x := by
  induction p using Result.cases with
  | ret v =>
    have hv : v = x := by simpa only [WP.spec_ok] using h
    simp [hv]
  | vis e k => exact False.elim ((WP.spec_vis ..).mp h)
  | div => exact False.elim ((WP.spec_div).mp h)

lemma rust_expanded_sbox_generation_correct :
    Magma.Rust.sboxes.gen_exp_sbox rustSboxTable = ok rustExpandedSbox := by
  exact
    result_eq_ok_of_spec _ _ (expanded_sbox_generation_correct rustSboxTable rust_sbox_entries_lt16)

theorem rust_expanded_sbox_constant_correct : rustSboxExt.EXP_SBOX = ok rustExpandedSbox := by
  change
    (do
        let a ← ok rustSboxTable;
        Magma.Rust.sboxes.gen_exp_sbox a) =
      ok rustExpandedSbox
  simpa only [bind_ok] using rust_expanded_sbox_generation_correct

end Magma.Proof

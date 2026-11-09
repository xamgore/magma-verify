module

public import Magma.RFC8891
public import Magma.Proof.Model

@[expose] public section

/-!
# The extracted substitution table and word arithmetic versus RFC 8891

These statements use the Aeneas-generated definitions, not a handwritten
Rust cipher model. The table equality covers every one of the 128 S-box
entries; the word arithmetic lemmas are valid for all 32-bit values.

The `round_function_matches_rfc_of_substitution` lemma identifies the *remaining*
proof obligation: the executable `apply_sbox` loop must implement
the RFC's `Magma.t`. It does NOT assume this has been proved.
-/

open Aeneas Aeneas.Std Result

namespace Magma.Proof

/-- The eight 16-entry substitution rows extracted by Aeneas. -/
def rustSboxTable : Aeneas.Std.Array (Aeneas.Std.Array Aeneas.Std.U8 16#usize) 8#usize :=
  Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox.SBOX

/-- For every row and column, the extracted S-box entry equals RFC 8891’s corresponding π entry. -/
theorem rust_table_matches_rfc (i : Fin 8) (j : Fin 16) :
    (((rustSboxTable.val[i.val]!).val[j.val]!).val) = (Magma.π'arrays i j).val := by
  fin_cases i <;> fin_cases j <;>
    (unfold rustSboxTable Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox.SBOX
     decide)

/-- The Aeneas model of Rust's wrapping addition is BitVec addition. -/
lemma wrapping_add_eq_bitvec_add (a k : Std.U32) :
    (core.num.U32.wrapping_add a k).bv = a.bv + k.bv := by
  simp

/-- The Aeneas model of Rust's left rotation agrees with the RFC. -/
lemma rotate_left_11_eq_rfc (x : Std.U32) :
    (core.num.U32.rotate_left x 11#u32).bv = Magma.rot11 x.bv := by
  rfl

/-- RFC addition in ZMod(2^32) is BitVec addition of the same words. -/
lemma rfc_modular_add_eq_bitvec_add (a k : BitVec 32) :
    Magma.Vec_s 32 (Magma.add₃₂ (Magma.Int_s 32 a) (Magma.Int_s 32 k)) =
      a + k := by
  simp [Magma.Vec_s, Magma.add₃₂, Magma.Int_s, ZMod.val_add]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- Aeneas's `step*` tactic verifies the adapter's input-read contract.
    This does not establish equivalence with the external cipher library. -/
lemma adapter_get_in_returns_input
    (io : Magma.Rust.adapter.InOut (Aeneas.Std.Array Std.U8 8#usize)) :
    Magma.Rust.adapter.InOutABArrayU88.get_in io ⦃ out => out = io.input ⦄ := by
  simp [Magma.Rust.adapter.InOutABArrayU88.get_in]

/-- The S-box extension instance used by the extracted substitution and round functions. -/
def rustSboxExt : Magma.Rust.sboxes.SboxExt Magma.Rust.sboxes.Tc26 :=
  Magma.Rust.sboxes.SboxExt.Blanket
    Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox

/-- If the executable S-box computation matches RFC's t, the entire
    generated Rust g implementation matches RFC's g. The premise is
    deliberately explicit and still requires a separate loop proof. -/
lemma round_function_matches_rfc_of_substitution (a k : Std.U32)
    (hsub :
      rustSboxExt.apply_sbox (core.num.U32.wrapping_add a k) =
      ok (⟨Magma.t (a.bv + k.bv)⟩ : Std.U32)) :
    Magma.Rust.sboxes.SboxExt.g.default rustSboxExt a k =
      ok (⟨Magma.g k.bv a.bv⟩ : Std.U32) := by
  have hs : rustSboxExt.apply_sbox (⟨a.bv + k.bv⟩ : Std.U32) =
      ok (⟨Magma.t (a.bv + k.bv)⟩ : Std.U32) := by
    simpa [core.num.U32.wrapping_add, UScalar.wrapping_add] using hsub
  simp [Magma.Rust.sboxes.SboxExt.g.default, lift, hs,
    Magma.g, Magma.rot11, rfc_modular_add_eq_bitvec_add,
    core.num.U32.wrapping_add, UScalar.wrapping_add,
    core.num.U32.rotate_left, UScalar.rotate_left]

end Magma.Proof

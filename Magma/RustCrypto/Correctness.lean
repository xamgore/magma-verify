module

public import Magma.RFC8891
public import Magma.RustCrypto.Tc26.Funs

@[expose] public section

/-!
# RustCrypto Tc26: first correspondence lemmas

These statements use the Aeneas-generated definitions, not a handwritten
Rust cipher model. The table equality covers every one of the 128 S-box
entries; the word arithmetic lemmas are valid for all 32-bit values.

The final `tc26_g_if_substitution` theorem identifies the *remaining*
proof obligation: the executable `apply_sbox` loop must implement
the RFC's `Magma.t`. It does NOT assume this has been proved.
-/

open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

/-- The actual Tc26 S-box table obtained from Aeneas. -/
def tc26Table : Aeneas.Std.Array (Aeneas.Std.Array Aeneas.Std.U8 16#usize) 8#usize :=
  RustCryptoTc26.sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox.SBOX

/-- All 8 × 16 entries of the RustCrypto Tc26 table equal the RFC 8891 tables. -/
theorem tc26_table_matches_rfc (i : Fin 8) (j : Fin 16) :
    (((tc26Table.val[i.val]!).val[j.val]!).val) = (Magma.π'arrays i j).val := by
  fin_cases i <;> fin_cases j <;>
    (unfold tc26Table RustCryptoTc26.sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox.SBOX
     decide)

/-- The Aeneas model of Rust's wrapping addition is BitVec addition. -/
theorem rust_wrapping_add (a k : Std.U32) :
    (core.num.U32.wrapping_add a k).bv = a.bv + k.bv := by
  simp

/-- The Aeneas model of Rust's left rotation agrees with the RFC. -/
theorem rust_rotate_left_11 (x : Std.U32) :
    (core.num.U32.rotate_left x 11#u32).bv = Magma.rot11 x.bv := by
  rfl

/-- RFC addition in ZMod(2^32) is BitVec addition of the same words. -/
theorem rfc_add_bv (a k : BitVec 32) :
    Magma.Vec_s 32 (Magma.add₃₂ (Magma.Int_s 32 a) (Magma.Int_s 32 k)) =
      a + k := by
  simp [Magma.Vec_s, Magma.add₃₂, Magma.Int_s, ZMod.val_add]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- Aeneas's `step*` tactic verifies the adapter's input-read contract.
    This does not establish equivalence with the external cipher library. -/
theorem adapter_get_in_correct {T : Type} (io : RustCryptoTc26.adapter.InOut T) :
    RustCryptoTc26.adapter.InOut.get_in io ⦃ out => out = io.input ⦄ := by
  unfold RustCryptoTc26.adapter.InOut.get_in
  step*

/-- The concrete RustCrypto Tc26 trait instance used by the generated model. -/
def tc26SboxExt : RustCryptoTc26.sboxes.SboxExt RustCryptoTc26.sboxes.Tc26 :=
  RustCryptoTc26.sboxes.SboxExt.Blanket
    RustCryptoTc26.sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox

/-- If the executable S-box computation matches RFC's t, the entire
    generated Rust g implementation matches RFC's g. The premise is
    deliberately explicit and still requires a separate loop proof. -/
theorem tc26_g_if_substitution (a k : Std.U32)
    (hsub :
      tc26SboxExt.apply_sbox (core.num.U32.wrapping_add a k) =
      ok (⟨Magma.t (a.bv + k.bv)⟩ : Std.U32)) :
    RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
      ok (⟨Magma.g k.bv a.bv⟩ : Std.U32) := by
  have hs : tc26SboxExt.apply_sbox (⟨a.bv + k.bv⟩ : Std.U32) =
      ok (⟨Magma.t (a.bv + k.bv)⟩ : Std.U32) := by
    simpa [core.num.U32.wrapping_add, UScalar.wrapping_add] using hsub
  simp [RustCryptoTc26.sboxes.SboxExt.g.default, lift, hs,
    Magma.g, Magma.rot11, rfc_add_bv,
    core.num.U32.wrapping_add, UScalar.wrapping_add,
    core.num.U32.rotate_left, UScalar.rotate_left]

end Magma.RustCrypto

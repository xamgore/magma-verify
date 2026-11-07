module

public import Magma.RustCrypto.SboxPacking
public import Magma.RustCrypto.Equivalence

@[expose] public section

/-!
# Unconditional Tc26 encryption correctness against RFC 8891

The Aeneas-generated, Tc26-specialized Rust model's original S-box loops,
`g`, and `encrypt_with_words` agree with the independent RFC 8891
specification for all inputs, without any substitution premise.

The verification-only I/O adapter's equivalence to the external `cipher`
library is not claimed, nor is a full decryption equivalence theorem.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

private theorem result_ok_of_spec {α : Type} (p : Result α) (x : α) (h : p ⦃ out => out = x ⦄) :
    p = ok x := by
  induction p using Result.cases with
  | ret v =>
    have hv : v = x := by simpa only [WP.spec_ok] using h
    simp [hv]
  | vis e k => exact False.elim ((WP.spec_vis ..).mp h)
  | div => exact False.elim ((WP.spec_div).mp h)

/-- Every Tc26 S-box input returns precisely RFC 8891's 32-bit substitution. -/
theorem tc26_apply_sbox_correct (a : Std.U32) :
    tc26SboxExt.apply_sbox a =
      ok (⟨Magma.t a.bv⟩ : Std.U32) := by
  have h := result_ok_of_spec _ _ (tc26_apply_model_spec a)
  have heq : tc26ApplyModel a = (⟨Magma.t a.bv⟩ : Std.U32) := by
    apply UScalar.eq_of_val_eq
    exact congrArg BitVec.toNat (tc26_model_matches_rfc a)
  exact h.trans (congrArg ok heq)

/-- The generated RustCrypto Tc26 round function is RFC 8891 `g`. -/
theorem tc26_g_correct (a k : Std.U32) :
    RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
      ok (⟨Magma.g k.bv a.bv⟩ : Std.U32) := by
  apply tc26_g_if_substitution
  simpa only [rust_wrapping_add] using
    (tc26_apply_sbox_correct (core.num.U32.wrapping_add a k))

/-- Unconditional, all-input byte-exact encryption refinement for the
    generated Tc26 Rust model. No `hg`, `sorry`, or extra axioms. -/
theorem encrypt_with_words_correct
    (key : Aeneas.Std.Array Std.U32 8#usize)
    (plain : Aeneas.Std.Array Std.U8 8#usize) :
    RustCryptoTc26.encrypt_with_words key plain ⦃ out =>
      out.val = rfcEncryptedBytes key plain ⦄ := by
  exact encrypt_with_words_if_g key plain tc26_g_correct

end Magma.RustCrypto

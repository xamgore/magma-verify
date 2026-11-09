module

public import Magma.Proof.Sbox.Packing
public import Magma.Proof.Encrypt.Equivalence

@[expose] public section

/-!
# Unconditional correctness of the extracted encryption method

The extracted S-box evaluation, round function `g` and block encryption
agree with the independent RFC 8891 specification for all inputs.
No unproved substitution premise remains.

The verification-only I/O adapter's equivalence to the external `cipher`
library is not claimed.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

private lemma result_ok_of_spec {α : Type} (p : Result α) (x : α) (h : p ⦃ out => out = x ⦄) :
    p = ok x := by
  induction p using Result.cases with
  | ret v =>
    have hv : v = x := by simpa only [WP.spec_ok] using h
    simp [hv]
  | vis e k => exact False.elim ((WP.spec_vis ..).mp h)
  | div => exact False.elim ((WP.spec_div).mp h)

/-- Every 32-bit input to the extracted S-box yields exactly the RFC substitution `t`. -/
theorem rust_apply_sbox_correct (a : Std.U32) :
    rustSboxExt.apply_sbox a = ok (⟨Magma.t a.bv⟩ : Std.U32) := by
  have h := result_ok_of_spec _ _ (rust_apply_sbox_matches_pure_model a)
  have heq : rustSboxModel a = (⟨Magma.t a.bv⟩ : Std.U32) := by
    apply UScalar.eq_of_val_eq
    exact congrArg BitVec.toNat (rust_model_matches_rfc a)
  exact h.trans (congrArg ok heq)

/-- The extracted modular addition, substitution and rotation implement RFC 8891 `g`. -/
theorem rust_g_correct (a k : Std.U32) :
    Magma.Rust.sboxes.SboxExt.g.default rustSboxExt a k = ok (⟨Magma.g k.bv a.bv⟩ : Std.U32) := by
  apply round_function_matches_rfc_of_substitution
  simpa only [wrapping_add_eq_bitvec_add] using
    (rust_apply_sbox_correct (core.num.U32.wrapping_add a k))

/-- The extracted block encryption method terminates and returns the RFC ciphertext. -/
theorem encrypt_block_correct
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (block : Magma.Rust.adapter.InOut (Aeneas.Std.Array Std.U8 8#usize)) :
    Rust.encrypt_block self block ⦃ out => out.output.val = rfcEncryptedBytes self.key block.input ⦄ := by
  simpa only [encrypted_bytes_match_rfc] using
    (encrypt_block_matches_expected_bytes_of_g_correct self block rust_g_correct)

end Magma.Proof

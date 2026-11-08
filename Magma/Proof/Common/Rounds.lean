module

public import Magma.Proof.Common.Foundations

@[expose] public section

/-!
# One generated RustCrypto Feistel step agrees with RFC 8891

These lemmas reason about the Aeneas-generated *inner loop body* from the
unchanged RustCrypto round algorithm. The hypotheses express the next
iterator value, the key lookup, and the as-yet-unproved S-box loop
correspondence. No properties of the generated loop are postulated.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

/-- A successful generated Rust loop-body step computes the Feistel update,
    provided the called Rust `g` returned the RFC value. -/
lemma encrypt_inner_loop_step
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hg :
      Magma.Rust.sboxes.SboxExt.g.default rustSboxExt r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32)) :
    Magma.Proof.Crate.encrypt_block_loop0_loop0.body self it l r =
      ok (cont (nextIt, r, (⟨l.bv ^^^ Magma.g key.bv r.bv⟩ : Std.U32))) := by
  have hg' :
      Magma.Rust.sboxes.SboxExt.g.default
        (Magma.Rust.sboxes.SboxExt.Blanket
          Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox) r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32) := by
    simpa only [rustSboxExt] using hg
  simp [Magma.Proof.Crate.encrypt_block_loop0_loop0.body,
    Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body,
    hnext, hkey, hg', lift]
  rfl

/-- Under a correctly implemented S-box, that same *generated loop body*
    performs exactly one RFC 8891 `Magma.G` Feistel round. -/
lemma encrypt_inner_loop_step_matches_rfc
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      rustSboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    Magma.Proof.Crate.encrypt_block_loop0_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hg := round_function_matches_rfc_of_substitution r key hsub
  rw [encrypt_inner_loop_step self it nextIt j key l r hnext hkey hg]
  simp [Magma.G, Magma.xor, BitVec.xor_comm]

/-- The generated first decryption loop performs the same RFC Feistel step. -/
lemma decrypt_forward_loop_step_matches_rfc
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      rustSboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    Magma.Proof.Crate.decrypt_block_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hbody :
      Magma.Proof.Crate.decrypt_block_loop0.body self it l r =
        Magma.Proof.Crate.encrypt_block_loop0_loop0.body self it l r := by
    rfl
  rw [hbody]
  exact encrypt_inner_loop_step_matches_rfc self it nextIt j key l r hnext hkey hsub

/-- The generated reverse-key decryption loop also computes one RFC Feistel step. -/
lemma decrypt_reverse_loop_step_matches_rfc
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it nextIt : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      rustSboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    Magma.Proof.Crate.decrypt_block_loop1_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hg := round_function_matches_rfc_of_substitution r key hsub
  have hg' :
      Magma.Rust.sboxes.SboxExt.g.default
        (Magma.Rust.sboxes.SboxExt.Blanket
          Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox) r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32) := by
    simpa only [rustSboxExt] using hg
  simp [Magma.Proof.Crate.decrypt_block_loop1_loop0.body,
    Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body,
    hnext, hkey, hg', lift]
  simp [Magma.G, Magma.xor, BitVec.xor_comm]
  rfl

end Magma.Proof

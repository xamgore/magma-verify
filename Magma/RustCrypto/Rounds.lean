module

public import Magma.RustCrypto.Correctness

@[expose] public section

/-!
# One generated RustCrypto Feistel step agrees with RFC 8891

These lemmas reason about the Aeneas-generated *inner loop body* from the
unchanged RustCrypto round algorithm. The hypotheses express the next
iterator value, the key lookup, and the as-yet-unproved S-box loop
correspondence. No properties of the generated loop are postulated.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

/-- A successful generated Rust loop-body step computes the Feistel update,
    provided the called Rust `g` returned the RFC value. -/
theorem encrypt_inner_step
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hg :
      RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.encrypt_block_loop0_loop0.body self it l r =
      ok (cont (nextIt, r, (⟨l.bv ^^^ Magma.g key.bv r.bv⟩ : Std.U32))) := by
  have hg' :
      RustCryptoTc26.sboxes.SboxExt.g.default
        (RustCryptoTc26.sboxes.SboxExt.Blanket
          RustCryptoTc26.sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox) r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32) := by
    simpa only [tc26SboxExt] using hg
  simp [RustCryptoTc26.Gost89Tc26.encrypt_block_loop0_loop0.body,
    RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body,
    hnext, hkey, hg', lift]
  rfl

/-- Under a correctly implemented S-box, that same *generated loop body*
    performs exactly one RFC 8891 `Magma.G` Feistel round. -/
theorem encrypt_inner_step_rfc
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      tc26SboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.encrypt_block_loop0_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hg := tc26_g_if_substitution r key hsub
  rw [encrypt_inner_step self it nextIt j key l r hnext hkey hg]
  simp [Magma.G, Magma.xor, BitVec.xor_comm]

/-- The generated first decryption loop performs the same RFC Feistel step. -/
theorem decrypt_forward_step_rfc
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it nextIt : core.ops.range.Range Std.Usize)
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      tc26SboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.decrypt_block_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hbody :
      RustCryptoTc26.Gost89Tc26.decrypt_block_loop0.body self it l r =
        RustCryptoTc26.Gost89Tc26.encrypt_block_loop0_loop0.body self it l r := by
    rfl
  rw [hbody]
  exact encrypt_inner_step_rfc self it nextIt j key l r hnext hkey hsub

/-- The generated reverse-key decryption loop also computes one RFC Feistel step. -/
theorem decrypt_reverse_step_rfc
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it nextIt : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (j : Std.Usize) (key l r : Std.U32)
    (hnext :
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) it =
        ok (some j, nextIt))
    (hkey : Array.index_usize self.key j = ok key)
    (hsub :
      tc26SboxExt.apply_sbox (core.num.U32.wrapping_add r key) =
        ok (⟨Magma.t (r.bv + key.bv)⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.decrypt_block_loop1_loop0.body self it l r =
      ok (cont (nextIt,
        (⟨(Magma.G key.bv (l.bv, r.bv)).1⟩ : Std.U32),
        (⟨(Magma.G key.bv (l.bv, r.bv)).2⟩ : Std.U32))) := by
  have hg := tc26_g_if_substitution r key hsub
  have hg' :
      RustCryptoTc26.sboxes.SboxExt.g.default
        (RustCryptoTc26.sboxes.SboxExt.Blanket
          RustCryptoTc26.sboxes.Tc26.Insts.Magma_tc26_sliceSboxesSbox) r key =
        ok (⟨Magma.g key.bv r.bv⟩ : Std.U32) := by
    simpa only [tc26SboxExt] using hg
  simp [RustCryptoTc26.Gost89Tc26.decrypt_block_loop1_loop0.body,
    RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body,
    hnext, hkey, hg', lift]
  simp [Magma.G, Magma.xor, BitVec.xor_comm]
  rfl

end Magma.RustCrypto

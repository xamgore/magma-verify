module

public import Magma.Proof.Common.Ranges

@[expose] public section

/-!
# Aeneas-generated inner encryption loop, all eight rounds

This is an actual total-correctness lemma for the original, *not unrolled*
inner RustCrypto encryption loop. The g-correctness premise is explicit;
the S-box implementation proof needed to discharge it is separate.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

/-- Pure auxiliary evaluator for consecutive Feistel rounds. -/
def runKeyRounds (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (start : Nat) : Nat → (BitVec 32 × BitVec 32) → (BitVec 32 × BitVec 32)
  | 0, state => state
  | n + 1, state =>
    runKeyRounds key (start + 1) n
      (Magma.G (key.val[start]!).bv state)

lemma run_key_rounds_step (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (start finish : Nat)
    (state : BitVec 32 × BitVec 32) (h : start < finish) :
    runKeyRounds key start (finish - start) state =
      runKeyRounds key (start + 1) (finish - (start + 1)) (Magma.G (key.val[start]!).bv state) := by
  have hn : finish - start = (finish - (start + 1)) + 1 := by omega
  rw [hn]
  rfl

/-- Full correctness and termination of the generated eight-step inner
    encryption loop, conditional on the Rust g operation agreeing with RFC g. -/
lemma encrypt_inner_loop_correct
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it : core.ops.range.Range Std.Usize) (l r : Std.U32)
    (hb : it.start.val ≤ it.end.val ∧ it.end.val ≤ 8)
    (hg : ∀ a k : Std.U32,
      Magma.Rust.sboxes.SboxExt.g.default rustSboxExt a k =
        ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    Magma.Proof.Crate.encrypt_block_loop0_loop0 it self l r
      ⦃ (outself : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
        (outl outr : Std.U32) =>
        outself = self ∧
          (outl.bv, outr.bv) =
            runKeyRounds self.key it.start.val (it.end.val - it.start.val)
              (l.bv, r.bv) ⦄ := by
  unfold Magma.Proof.Crate.encrypt_block_loop0_loop0
  unfold Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun s => s.1.end.val - s.1.start.val)
    (inv := fun s =>
      s.1.end = it.end ∧ s.1.start.val ≤ it.end.val ∧
      runKeyRounds self.key s.1.start.val
        (it.end.val - s.1.start.val) (s.2.1.bv, s.2.2.bv) =
          runKeyRounds self.key it.start.val (it.end.val - it.start.val)
            (l.bv, r.bv))
  · intro s hs
    rcases s with ⟨it', left', right'⟩
    rcases hs with ⟨hend, hbound, hpure⟩
    dsimp only [Prod.fst, Prod.snd] at hend hbound hpure ⊢
    by_cases hstep : it'.start.val < it'.end.val
    · have hi : it'.start.val < 8 := by
        have hlt : it'.start.val < it.end.val := by
          simpa only [hend] using hstep
        omega
      have hnext := usize_range_next_some it' hstep
      unfold Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body
      step with hnext
      subst o
      have hkey := key_index_in_bounds self.key it'.start hi
      have hg0 := hg right' (self.key.val[it'.start.val]!)
      have hg' :
          Magma.Rust.sboxes.SboxExt.g.default
            (Magma.Rust.sboxes.SboxExt.Blanket
              Magma.Rust.sboxes.Tc26.Insts.MagmaSboxesSbox)
            right' (self.key.val[it'.start.val]!) =
            ok (⟨Magma.g (self.key.val[it'.start.val]!).bv right'.bv⟩ : Std.U32) := by
        simpa only [rustSboxExt] using hg0
      simp only [hkey, hg', bind_ok, lift]
      simp only [WP.spec_ok]
      have hlt : it'.start.val < it.end.val := by simpa only [hend] using hstep
      have hfeistel :
          (right'.bv,
            (left' ^^^
              (⟨Magma.g (self.key.val[it'.start.val]!).bv right'.bv⟩ : Std.U32)).bv) =
            Magma.G (self.key.val[it'.start.val]!).bv (left'.bv, right'.bv) := by
        simp [Magma.G, Magma.xor, BitVec.xor_comm]
      refine ⟨o_post2.trans hend, ?_, ?_, ?_⟩
      · have he := congrArg UScalar.val (o_post2.trans hend)
        omega
      · rw [o_post1, hfeistel]
        exact (run_key_rounds_step self.key it'.start.val it.end.val
          (left'.bv, right'.bv) hlt).symm.trans hpure
      · have he := congrArg UScalar.val o_post2
        omega
    · have hnone : it'.end.val ≤ it'.start.val := by omega
      have hnext := usize_range_next_none it' hnone
      unfold Magma.Rust.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0_loop0.body
      step with hnext
      subst o
      simp only [WP.spec_ok, true_and]
      have hendStart : it'.start.val = it.end.val := by
        have he := congrArg UScalar.val hend
        omega
      have hzero : it.end.val - it'.start.val = 0 := by omega
      simpa [hzero, runKeyRounds] using hpure
  · simp [hb]

/-- The first eight decryption rounds reuse the very same generated body. -/
lemma decrypt_forward_loop_correct
    (self : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
    (it : core.ops.range.Range Std.Usize) (l r : Std.U32)
    (hb : it.start.val ≤ it.end.val ∧ it.end.val ≤ 8)
    (hg : ∀ a k : Std.U32,
      Magma.Rust.sboxes.SboxExt.g.default rustSboxExt a k =
        ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    Magma.Proof.Crate.decrypt_block_loop0 it self l r
      ⦃ (outself : Magma.Rust.Gost89 Magma.Rust.sboxes.Tc26)
        (outl outr : Std.U32) =>
        outself = self ∧
          (outl.bv, outr.bv) =
            runKeyRounds self.key it.start.val (it.end.val - it.start.val)
              (l.bv, r.bv) ⦄ := by
  have same_loop :
      Magma.Proof.Crate.decrypt_block_loop0 it self l r =
        Magma.Proof.Crate.encrypt_block_loop0_loop0 it self l r := by
    rfl
  rw [same_loop]
  exact encrypt_inner_loop_correct self it l r hb hg

end Magma.Proof

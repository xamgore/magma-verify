module

public import Magma.RustCrypto.Outer

@[expose] public section

/-!
# Entire reverse-key pass of the original RustCrypto encryption loop

The Aeneas `Rev<Range<Usize>>` iterator is checked directly, including the
decrement of its upper bound. No Rust cipher rounds are rewritten.
-/

open Aeneas Aeneas.Std Result

namespace Magma.RustCrypto

theorem rust_reverse_next_some (it : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (hlt : it.iter.start.val < it.iter.end.val) (hbound : it.iter.end.val ≤ 8) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it ⦃
      (o : Option Std.Usize) (it' : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) =>
      o = some it'.iter.end ∧
        it'.iter.start = it.iter.start ∧ it'.iter.end.val + 1 = it.iter.end.val ⦄ := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked]
  have hpos : (1#usize).val ≤ it.iter.end.val := by
    have hone : (1#usize).val = 1 := by rfl
    rw [hone]
    omega
  simp only [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt, decide_true, ↓reduceIte, bind_ok,
    hpos, ↓reduceDIte]
  simp [UScalar.ofNatCore_val_eq]
  omega

theorem rust_reverse_next_none (it : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (hge : it.iter.end.val ≤ it.iter.start.val) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
        (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) it ⦃
      (o : Option Std.Usize) (it' : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) =>
      o = none ∧ it' = it ⦄ := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked]
  simp only [liftFun2, core.cmp.impls.PartialOrdUsize.lt, bind_ok]
  have hn : ¬it.iter.start.val < it.iter.end.val := by omega
  simp [hn, WP.spec_ok]

/-- Pure function for the descending subkeys. -/
def runReverseRounds (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
    (start : Nat) : Nat → (BitVec 32 × BitVec 32) → (BitVec 32 × BitVec 32)
  | 0, state => state
  | n + 1, state =>
    runReverseRounds key start n (Magma.G (key.val[start+n]!).bv state)

theorem runReverseRounds_step (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (start finish : Nat)
    (s : BitVec 32 × BitVec 32) (h : start < finish) :
    runReverseRounds key start (finish - start) s =
      runReverseRounds key start (finish - 1 - start) (Magma.G (key.val[finish - 1]!).bv s) := by
  have hn : finish - start = (finish - 1 - start) + 1 := by omega
  rw [hn]
  simp only [runReverseRounds]
  have hk : start + (finish - 1 - start) = finish - 1 := by omega
  rw [hk]

/-- All eight descending key rounds of the generated encryption loop. -/
theorem encrypt_reverse_loop_spec
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (l r : Std.U32)
    (hb : it.iter.start.val ≤ it.iter.end.val ∧ it.iter.end.val ≤ 8)
    (hg : ∀ a k : Std.U32,
      RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
        ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.Tc26.encrypt_block_loop1 it self l r
      ⦃ (outl outr : Std.U32) =>
        (outl.bv, outr.bv) =
          runReverseRounds self.key it.iter.start.val
            (it.iter.end.val-it.iter.start.val) (l.bv, r.bv) ⦄ := by
  unfold RustCryptoTc26.Tc26.encrypt_block_loop1
  unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1
  apply loop.spec_decr_nat
    (measure := fun s => s.1.iter.end.val - s.1.iter.start.val)
    (inv := fun s =>
      s.1.iter.start = it.iter.start ∧
      s.1.iter.start.val ≤ s.1.iter.end.val ∧
      s.1.iter.end.val ≤ 8 ∧
      runReverseRounds self.key it.iter.start.val
        (s.1.iter.end.val - it.iter.start.val) (s.2.1.bv, s.2.2.bv) =
          runReverseRounds self.key it.iter.start.val
            (it.iter.end.val - it.iter.start.val) (l.bv,r.bv))
  · intro s hs
    rcases s with ⟨it', left', right'⟩
    rcases hs with ⟨hstart,hbound,hend,hpure⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : it'.iter.start.val < it'.iter.end.val
    · have hnext := rust_reverse_next_some it' hstep hend
      unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body
      step with hnext
      subst o
      have hi : iter1.iter.end.val < 8 := by omega
      have hkey := rust_key_index_ok self.key iter1.iter.end hi
      have hg0 := hg right' (self.key.val[iter1.iter.end.val]!)
      have hg' :
          RustCryptoTc26.sboxes.SboxExt.g.default
            (RustCryptoTc26.sboxes.SboxExt.Blanket
              RustCryptoTc26.sboxes.Tc26.Insts.MagmaSboxesSbox)
            right' (self.key.val[iter1.iter.end.val]!) =
            ok (⟨Magma.g (self.key.val[iter1.iter.end.val]!).bv right'.bv⟩ : Std.U32) := by
        simpa only [tc26SboxExt] using hg0
      simp only [hkey, hg', bind_ok, lift, WP.spec_ok]
      have hlt : it.iter.start.val < it'.iter.end.val := by
        have hs := congrArg UScalar.val hstart
        omega
      have hnewend : iter1.iter.end.val = it'.iter.end.val - 1 := by omega
      have hfeistel :
          (right'.bv,
            (left' ^^^
              (⟨Magma.g (self.key.val[iter1.iter.end.val]!).bv right'.bv⟩ : Std.U32)).bv) =
            Magma.G (self.key.val[iter1.iter.end.val]!).bv (left'.bv, right'.bv) := by
        simp [Magma.G, Magma.xor, BitVec.xor_comm]
      refine ⟨o_post1.trans hstart, ?_, ?_, ?_, ?_⟩
      · have hs := congrArg UScalar.val (o_post1.trans hstart)
        omega
      · omega
      · rw [hfeistel, hnewend]
        exact (runReverseRounds_step self.key it.iter.start.val it'.iter.end.val
          (left'.bv,right'.bv) hlt).symm.trans hpure
      · have hs := congrArg UScalar.val o_post1
        omega
    · have hge : it'.iter.end.val ≤ it'.iter.start.val := by omega
      have hnext := rust_reverse_next_none it' hge
      unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop1.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hzero : it'.iter.end.val - it.iter.start.val = 0 := by
        have hs := congrArg UScalar.val hstart
        omega
      simpa [hzero, runReverseRounds] using hpure
  · simp [hb]

end Magma.RustCrypto

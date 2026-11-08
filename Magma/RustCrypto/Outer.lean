module

public import Magma.RustCrypto.Loops

@[expose] public section

/-!
# Three full forward passes through the generated RustCrypto inner loop

The proof uses `loop.spec_decr_nat` on the original outer I32 iterator.
Correctness is conditional only on the generated S-box `g` contract.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

theorem rust_i32_range_next (it : core.ops.range.Range Std.I32) (hlt : it.start.val < it.end.val)
    (hmax : it.end.val ≤ 3) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 it ⦃
      (o : Option Std.I32) (it' : core.ops.range.Range Std.I32) =>
      o = some it.start ∧ it'.start.val = it.start.val + 1 ∧ it'.end = it.end ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.iter.range.IScalarStep.forward_checked]
  simp only [liftFun2, liftFun1, core.cmp.impls.PartialOrdI32.lt, core.clone.impls.CloneI32.clone,
    hlt, decide_true, ↓reduceIte, bind_ok]
  have hfwd : it.start.val + (1#usize).val ≤ IScalar.max .I32 := by
    have hnum : IScalar.max .I32 = 2147483647 := by simp [I32.max_eq]
    rw [hnum]
    norm_num
    omega
  simp only [hfwd, ↓reduceDIte, bind_ok, WP.spec_ok]
  simp

theorem rust_i32_range_next_none (it : core.ops.range.Range Std.I32)
    (hge : it.end.val ≤ it.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 it ⦃
      (o : Option Std.I32) (it' : core.ops.range.Range Std.I32) => o = none ∧ it' = it ⦄ := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepI32,
    core.iter.range.IScalarStep, core.cmp.impls.PartialOrdI32.lt, liftFun2, bind_ok]
  have hn : ¬it.start.val < it.end.val := by omega
  simp [hn, WP.spec_ok]

/-- Repeat the original eight-word key pattern n times. -/
def repeat8Rounds (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
  : Nat → (BitVec 32 × BitVec 32) → (BitVec 32 × BitVec 32)
  | 0, state => state
  | n + 1, state =>
    repeat8Rounds key n (runKeyRounds key 0 8 state)

theorem repeat8Rounds_int_step (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (j : Int)
    (state : BitVec 32 × BitVec 32) (h : 0 ≤ j ∧ j < 3) :
    repeat8Rounds key (3 - j).toNat state =
      repeat8Rounds key (3 - (j + 1)).toNat (runKeyRounds key 0 8 state) := by
  have hj : (3 - j).toNat = (3 - (j + 1)).toNat + 1 := by omega
  rw [hj]
  rfl

theorem encrypt_three_loops_spec (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (l r : Std.U32)
    (hg :
      ∀ a k : Std.U32,
        RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
          ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.Gost89Tc26.encrypt_block_loop0 { start := 0#i32, «end» := 3#i32 } self l r ⦃
      (outself : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26) (outl outr : Std.U32) =>
      outself = self ∧ (outl.bv, outr.bv) = repeat8Rounds self.key 3 (l.bv, r.bv) ⦄ := by
  unfold RustCryptoTc26.Gost89Tc26.encrypt_block_loop0
  unfold
    RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0
  apply
    loop.spec_decr_nat (measure := fun s => (3 - s.1.start.val).toNat) (inv := fun s =>
      s.1.end = 3#i32 ∧
        0 ≤ s.1.start.val ∧
        s.1.start.val ≤ 3 ∧
        s.2.1 = self ∧
        repeat8Rounds self.key (3 - s.1.start.val).toNat (s.2.2.1.bv, s.2.2.2.bv) =
          repeat8Rounds self.key 3 (l.bv, r.bv))
  · intro s hs
    rcases s with ⟨it', self', left', right'⟩
    rcases hs with ⟨hend, hlo, hhi, hself, hpure⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : it'.start.val < it'.end.val
    · have hthree : (3#i32).val = 3 := by rfl
      have hnext :=
        rust_i32_range_next it' hstep
          (by
            have hval := congrArg IScalar.val hend
            omega)
      unfold
        RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body
      step with hnext
      subst o
      subst self'
      have hinner :=
        encrypt_inner_loop_spec self { start := 0#usize, «end» := 8#usize } left' right' (by decide)
          hg
      step with hinner
      have hlt : it'.start.val < 3 := by
        have hh := congrArg IScalar.val hend
        omega
      refine ⟨o_post2.trans hend, ?_, ?_, r_post, ?_, ?_⟩
      · omega
      · omega
      · rw [o_post1, r_post1]
        exact
          (repeat8Rounds_int_step self.key it'.start.val (left'.bv, right'.bv)
                ⟨hlo, hlt⟩).symm.trans
            hpure
      · omega
    · have hthree : (3#i32).val = 3 := by rfl
      have hge : it'.end.val ≤ it'.start.val := by omega
      have hnext := rust_i32_range_next_none it' hge
      unfold
        RustCryptoTc26.Gost89.Insts.Magma_tc26_sliceAdapterBlockCipherEncBackendArrayU88.encrypt_block_loop0.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hstart : it'.start.val = 3 := by
        have hh := congrArg IScalar.val hend
        omega
      have hzero : (3 - it'.start.val).toNat = 0 := by omega
      simpa [hself, hzero, repeat8Rounds] using hpure
  · norm_num [repeat8Rounds]

end Magma.RustCrypto

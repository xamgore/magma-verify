module

public import Magma.RustCrypto.SboxFinal

@[expose] public section

/-! Reverse-key decryption loop over the original Aeneas body. -/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

/-- All eight descending key rounds of the generated decryption loop. -/
theorem decrypt_reverse_loop_spec
    (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
    (l r : Std.U32)
    (hb : it.iter.start.val ≤ it.iter.end.val ∧ it.iter.end.val ≤ 8)
    (hg : ∀ a k : Std.U32,
      RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
        ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.Tc26.decrypt_block_loop1_loop0 it self l r
      ⦃ (outself : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
        (outl outr : Std.U32) =>
        outself = self ∧ (outl.bv, outr.bv) =
          runReverseRounds self.key it.iter.start.val
            (it.iter.end.val-it.iter.start.val) (l.bv, r.bv) ⦄ := by
  unfold RustCryptoTc26.Tc26.decrypt_block_loop1_loop0
  unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0
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
      unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body
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
      unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1_loop0.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hzero : it'.iter.end.val - it.iter.start.val = 0 := by
        have hs := congrArg UScalar.val hstart
        omega
      simpa [hzero, runReverseRounds] using hpure
  · simp [hb]

/-- Repeat the original eight-word key pattern n times. -/
def repeatReverse8Rounds (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize)
  : Nat → (BitVec 32 × BitVec 32) → (BitVec 32 × BitVec 32)
  | 0, state => state
  | n + 1, state =>
    repeatReverse8Rounds key n (runReverseRounds key 0 8 state)

theorem repeatReverse8Rounds_int_step (key : Aeneas.Std.Array Aeneas.Std.U32 8#usize) (j : Int)
    (state : BitVec 32 × BitVec 32) (h : 0 ≤ j ∧ j < 3) :
    repeatReverse8Rounds key (3 - j).toNat state =
      repeatReverse8Rounds key (3 - (j + 1)).toNat (runReverseRounds key 0 8 state) := by
  have hj : (3 - j).toNat = (3 - (j + 1)).toNat + 1 := by omega
  rw [hj]
  rfl

theorem decrypt_three_reverse_loops_spec (self : RustCryptoTc26.Gost89 RustCryptoTc26.sboxes.Tc26)
    (l r : Std.U32)
    (hg :
      ∀ a k : Std.U32,
        RustCryptoTc26.sboxes.SboxExt.g.default tc26SboxExt a k =
          ok (⟨Magma.g k.bv a.bv⟩ : Std.U32)) :
    RustCryptoTc26.Tc26.decrypt_block_loop1 { start := 0#i32, «end» := 3#i32 } self l r ⦃
      (outl outr : Std.U32) =>
      (outl.bv, outr.bv) = repeatReverse8Rounds self.key 3 (l.bv, r.bv) ⦄ := by
  unfold RustCryptoTc26.Tc26.decrypt_block_loop1
  unfold RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1
  apply
    loop.spec_decr_nat (measure := fun s => (3 - s.1.start.val).toNat) (inv := fun s =>
      s.1.end = 3#i32 ∧
        0 ≤ s.1.start.val ∧
        s.1.start.val ≤ 3 ∧
        s.2.1 = self ∧
        repeatReverse8Rounds self.key (3 - s.1.start.val).toNat (s.2.2.1.bv, s.2.2.2.bv) =
          repeatReverse8Rounds self.key 3 (l.bv, r.bv))
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
        RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body
      step with hnext
      subst o
      subst self'
      simp only [core.iter.traits.iterator.Iterator.rev.trait_default,
        core.iter.traits.iterator.Iterator.rev.default, bind_ok]
      have hinner :=
        decrypt_reverse_loop_spec self ⟨{ start := 0#usize, «end» := 8#usize }⟩ left' right'
          (by decide) hg
      step with hinner
      have hlt : it'.start.val < 3 := by
        have hh := congrArg IScalar.val hend
        omega
      refine ⟨o_post2.trans hend, ?_, ?_, self1_post, ?_, ?_⟩
      · omega
      · omega
      · rw [o_post1, self1_post1]
        exact
          (repeatReverse8Rounds_int_step self.key it'.start.val (left'.bv, right'.bv)
                ⟨hlo, hlt⟩).symm.trans
            hpure
      · omega
    · have hthree : (3#i32).val = 3 := by rfl
      have hge : it'.end.val ≤ it'.start.val := by omega
      have hnext := rust_i32_range_next_none it' hge
      unfold
        RustCryptoTc26.Gost89.Insts.MagmaAdapterBlockCipherDecBackendArrayU88.decrypt_block_loop1.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hstart : it'.start.val = 3 := by
        have hh := congrArg IScalar.val hend
        omega
      have hzero : (3 - it'.start.val).toNat = 0 := by omega
      simpa [hself, hzero, repeatReverse8Rounds] using hpure
  · norm_num [repeatReverse8Rounds]

end Magma.RustCrypto

module

public import Magma.RustCrypto.SboxGeneration

@[expose] public section

/-!
# Three original nested loops in expanded S-box construction

All 4×16×16 iterations are proved to terminate, have in-bounds accesses,
and produce the exact `expWrite` sequence from the Aeneas-translated
RustCrypto source. No source-loop unrolling and no additional proof assumptions.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.RustCrypto

theorem expNextK_val (k : Std.Usize) (hk : k.val < 16) : (expNextK k).val = k.val + 1 := by
  simp only [expNextK, UScalar.wrapping_add_val_eq]
  have hsize : k.val + 1 < UScalar.size .Usize := by
    simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h
    · rw [h]; norm_num; omega
    · rw [h]; norm_num; omega
  have hsize' : k.val + 1 < Usize.size := by simpa only [UScalar.size_UScalarTyUsize] using hsize
  simpa only [show (1#usize).val = 1 by rfl, UScalar.size_UScalarTyUsize] using
    (Nat.mod_eq_of_lt hsize')

/-- Evaluation of n successive original S-box expansion writes from k. -/
def expFillK (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (i j : Std.Usize) : Nat →
       Std.Usize → Std.Array (Std.Array Std.U8 256#usize) 4#usize →
         Std.Array (Std.Array Std.U8 256#usize) 4#usize
  | 0, _, out => out
  | n + 1, k, out => expFillK sbox i j n (expNextK k) (expWrite sbox out i j k)

theorem expFillK_step (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i j k : Std.Usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (hk : k.val < 16) :
    expFillK sbox i j (16 - k.val) k out =
      expFillK sbox i j (16 - (expNextK k).val) (expNextK k) (expWrite sbox out i j k) := by
  have hn : 16 - k.val = 16 - (expNextK k).val + 1 := by
    rw [expNextK_val k hk]; omega
  rw [hn]
  rfl

theorem gen_exp_inner_loop (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (i j k : Std.Usize) (hi : i.val < 4)
    (hj : j.val < 16) (hk : k.val ≤ 16)
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16, ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0_loop0 sbox out i j k ⦃ out1 =>
      out1 = expFillK sbox i j (16 - k.val) k out ⦄ := by
  unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0_loop0
  apply
    loop.spec_decr_nat (measure := fun s => 16 - s.2.val) (inv := fun s =>
      s.2.val ≤ 16 ∧
        expFillK sbox i j (16 - s.2.val) s.2 s.1 = expFillK sbox i j (16 - k.val) k out)
  · intro s hs
    rcases s with ⟨out', k'⟩
    rcases hs with ⟨hb, hpure⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : k'.val < 16
    · have hbody := gen_exp_inner_step sbox out' i j k' hi hj hstep hvals
      step with hbody
      simp only [r_post]
      refine ⟨?_, ?_, ?_⟩
      · rw [expNextK_val k' hstep]
        omega
      · exact (expFillK_step sbox i j k' out' hstep).symm.trans hpure
      · rw [expNextK_val k' hstep]
        omega
    · unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0_loop0.body
      simp [hstep, WP.spec_ok]
      have heq : k'.val = 16 := by omega
      simpa [heq, expFillK] using hpure
  · simp [hk]

def expFillJ (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i : Std.Usize) :
    Nat →
      Std.Usize →
      Std.Array (Std.Array Std.U8 256#usize) 4#usize →
      Std.Array (Std.Array Std.U8 256#usize) 4#usize
  | 0, _, out => out
  | n + 1, j, out => expFillJ sbox i n (expNextK j) (expFillK sbox i j 16 0#usize out)

theorem expFillJ_step (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i j : Std.Usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (hj : j.val < 16) :
    expFillJ sbox i (16 - j.val) j out =
      expFillJ sbox i (16 - (expNextK j).val) (expNextK j) (expFillK sbox i j 16 0#usize out) := by
  have hn : 16 - j.val = 16 - (expNextK j).val + 1 := by
    rw [expNextK_val j hj]; omega
  rw [hn]
  rfl

theorem gen_exp_middle_loop (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (i j : Std.Usize) (hi : i.val < 4)
    (hj : j.val ≤ 16)
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16, ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0 sbox out i j ⦃ out1 =>
      out1 = expFillJ sbox i (16 - j.val) j out ⦄ := by
  unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0
  apply
    loop.spec_decr_nat (measure := fun s => 16 - s.2.val) (inv := fun s =>
      s.2.val ≤ 16 ∧ expFillJ sbox i (16 - s.2.val) s.2 s.1 = expFillJ sbox i (16 - j.val) j out)
  · intro s hs
    rcases s with ⟨out', j'⟩
    rcases hs with ⟨hb, hpure⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : j'.val < 16
    · have hinner := gen_exp_inner_loop sbox out' i j' 0#usize hi hstep (by decide) hvals
      unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0.body
      have hlt : j' < 16#usize := by simpa using hstep
      simp only [hlt, ↓reduceIte]
      step with hinner
      step
      have hnext : j1 = expNextK j' := by
        apply UScalar.eq_of_val_eq
        rw [j1_post, expNextK_val j' hstep]
      subst j1
      refine ⟨?_, ?_, ?_⟩
      · rw [expNextK_val j' hstep]; omega
      · rw [out1_post]
        exact (expFillJ_step sbox i j' out' hstep).symm.trans hpure
      · rw [expNextK_val j' hstep]; omega
    · unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0_loop0.body
      simp [hstep, WP.spec_ok]
      have heq : j'.val = 16 := by omega
      simpa [heq, expFillJ] using hpure
  · simp [hj]

def expFillI (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) :
    Nat →
      Std.Usize →
      Std.Array (Std.Array Std.U8 256#usize) 4#usize →
      Std.Array (Std.Array Std.U8 256#usize) 4#usize
  | 0, _, out => out
  | n + 1, i, out => expFillI sbox n (expNextK i) (expFillJ sbox i 16 0#usize out)

theorem expFillI_step (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize) (i : Std.Usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (hi : i.val < 4) :
    expFillI sbox (4 - i.val) i out =
      expFillI sbox (4 - (expNextK i).val) (expNextK i) (expFillJ sbox i 16 0#usize out) := by
  have hn : 4 - i.val = 4 - (expNextK i).val + 1 := by
    rw [expNextK_val i (by omega)]; omega
  rw [hn]
  rfl

theorem gen_exp_outer_loop (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (out : Std.Array (Std.Array Std.U8 256#usize) 4#usize) (i : Std.Usize) (hi : i.val ≤ 4)
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16, ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    RustCryptoTc26.sboxes.gen_exp_sbox_loop0 sbox out i ⦃ out1 =>
      out1 = expFillI sbox (4 - i.val) i out ⦄ := by
  unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0
  apply
    loop.spec_decr_nat (measure := fun s => 4 - s.2.val) (inv := fun s =>
      s.2.val ≤ 4 ∧ expFillI sbox (4 - s.2.val) s.2 s.1 = expFillI sbox (4 - i.val) i out)
  · intro s hs
    rcases s with ⟨out', i'⟩
    rcases hs with ⟨hb, hpure⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : i'.val < 4
    · have hinner := gen_exp_middle_loop sbox out' i' 0#usize hstep (by decide) hvals
      unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0.body
      have hlt : i' < 4#usize := by simpa using hstep
      simp only [hlt, ↓reduceIte]
      step with hinner
      step
      have hnext : i1 = expNextK i' := by
        apply UScalar.eq_of_val_eq
        rw [i1_post, expNextK_val i' (by omega)]
      subst i1
      refine ⟨?_, ?_, ?_⟩
      · rw [expNextK_val i' (by omega)]; omega
      · rw [out1_post]
        exact (expFillI_step sbox i' out' hstep).symm.trans hpure
      · rw [expNextK_val i' (by omega)]; omega
    · unfold RustCryptoTc26.sboxes.gen_exp_sbox_loop0.body
      simp [hstep, WP.spec_ok]
      have heq : i'.val = 4 := by omega
      simpa [heq, expFillI] using hpure
  · simp [hi]

theorem gen_exp_sbox_full (sbox : Std.Array (Std.Array Std.U8 16#usize) 8#usize)
    (hvals : ∀ ii : Fin 8, ∀ jj : Fin 16, ((sbox.val[ii.val]!).val[jj.val]!).val < 16) :
    RustCryptoTc26.sboxes.gen_exp_sbox sbox ⦃ out =>
      out =
        expFillI sbox 4 0#usize (Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u8)) ⦄ := by
  unfold RustCryptoTc26.sboxes.gen_exp_sbox
  step
    with(gen_exp_outer_loop sbox (Std.Array.repeat 4#usize (Std.Array.repeat 256#usize 0#u8))
      0#usize (by decide) hvals)
  simpa only [show (0#usize).val = 0 by rfl, Nat.sub_zero] using out_post

end Magma.RustCrypto

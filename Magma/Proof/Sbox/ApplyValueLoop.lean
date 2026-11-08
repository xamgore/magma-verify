module

public import Magma.Proof.Sbox.ApplyValue

@[expose] public section

/-!
# Exact iteration invariant for the original apply_sbox

This module proves the exact value of all four original Aeneas
`apply_sbox` iterations for any input word; no loop expansion,
unproved theorem, or native evaluator axiom.
-/

set_option maxRecDepth 4096
open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

/-- Apply the faithful pure S-box step n times from an iterator index. -/
def tc26Steps (a : Std.U32) : Nat → Std.Usize → Std.U32 → Std.U32
  | 0, _, v => v
  | n + 1, i, v => tc26Steps a n (expNextK i) (tc26Step a i v)

theorem tc26Steps_step (a v : Std.U32) (i : Std.Usize) (endIdx : Nat) (hi : i.val < endIdx)
    (hend : endIdx ≤ 4) :
    tc26Steps a (endIdx - i.val) i v =
      tc26Steps a (endIdx - (expNextK i).val) (expNextK i) (tc26Step a i v) := by
  have hn : endIdx - i.val = endIdx - (expNextK i).val + 1 := by
    have hi16 : i.val < 16 := by omega
    rw [expNextK_val i hi16]
    omega
  rw [hn]
  rfl

/-- Exact full-loop result and termination. -/
theorem apply_sbox_loop_value (a v : Std.U32)
    (iter : core.ops.range.Range Std.Usize)
    (hb : iter.start.val ≤ iter.end.val ∧ iter.end.val ≤ 4)
    (hv : v.val < 2^(8*iter.start.val)) :
    Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop tc26SboxExt iter a v
      ⦃ out => out = tc26Steps a (iter.end.val - iter.start.val) iter.start v ⦄ := by
  unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop
  apply loop.spec_decr_nat
    (measure := fun s => s.1.end.val - s.1.start.val)
    (inv := fun s => s.1.end = iter.end ∧
      s.1.start.val ≤ iter.end.val ∧
      s.2.val < 2^(8*s.1.start.val) ∧
      tc26Steps a (iter.end.val - s.1.start.val) s.1.start s.2 =
        tc26Steps a (iter.end.val - iter.start.val) iter.start v)
  · intro s hs
    rcases s with ⟨it, acc⟩
    rcases hs with ⟨hend, hbound, hval, hacc⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : it.start.val < it.end.val
    · have hlt : it.end.val ≤ 4 := by simpa [hend] using hb.2
      have hbody := apply_sbox_step_value a acc it hstep hlt hval
      step with hbody
      simp only [r_post]
      have hnew : it'.start = expNextK it.start := by
        apply UScalar.eq_of_val_eq
        rw [r_post1, expNextK_val it.start (by omega)]
      have hrec : tc26Steps a (iter.end.val - it'.start.val) it'.start v' =
          tc26Steps a (iter.end.val - it.start.val) it.start acc := by
        rw [hnew, v'_post]
        exact (tc26Steps_step a acc it.start iter.end.val
          (by have he := congrArg UScalar.val hend; omega) hb.2).symm
      refine ⟨r_post2.trans hend, ?_, r_post3, hrec.trans hacc, ?_⟩
      · have he := congrArg UScalar.val hend
        omega
      · have he := congrArg UScalar.val r_post2
        omega
    · have hnone : it.end.val ≤ it.start.val := by omega
      have hnext := rust_usize_range_next_none it hnone
      unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hfinal : it.start.val = iter.end.val := by
        have h := congrArg UScalar.val hend
        omega
      simpa [hfinal, tc26Steps] using hacc
  · exact ⟨rfl, hb.1, hv, rfl⟩

/-- Pure value of the original four-step Tc26 substitution. -/
def tc26ApplyModel (a : Std.U32) : Std.U32 := tc26Steps a 4 0#usize 0#u32

theorem tc26_apply_model_spec (a : Std.U32) :
    tc26SboxExt.apply_sbox a ⦃ out => out = tc26ApplyModel a ⦄ := by
  change
    Magma.Rust.sboxes.SboxExt.apply_sbox.default tc26SboxExt a ⦃ out => out = tc26ApplyModel a ⦄
  unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default
  step
    with(apply_sbox_loop_value a 0#u32 { start := 0#usize, «end» := 4#usize } (by decide)
      (by decide))
  simpa only [tc26ApplyModel, show (4#usize).val = 4 by rfl, show (0#usize).val = 0 by rfl,
    Nat.sub_zero] using out_post

end Magma.Proof

module

public import Magma.Proof.Sbox.Apply

@[expose] public section

/-!
# Original four-step apply_sbox loop: total correctness and bounds

The original Aeneas-translated `apply_sbox` loop terminates for every U32
input. Each of its four iterations is proved to stay within the expanded
S-box and preserve the invariant that already-computed result bytes
fit inside their bit positions.

This module proves safety and termination. Exact equality to RFC `t`
remains separate and is not asserted here.
-/

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

/-- End-of-loop bound after each completed byte, with total termination. -/
theorem apply_sbox_loop_total
    (a v : Std.U32) (iter : core.ops.range.Range Std.Usize)
    (hb : iter.start.val ≤ iter.end.val ∧ iter.end.val ≤ 4)
    (hv : v.val < 2^(8*iter.start.val)) :
    Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop tc26SboxExt iter a v
      ⦃ out => out.val < 2^(8*iter.end.val) ⦄ := by
  unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop
  apply loop.spec_decr_nat
    (measure := fun s => s.1.end.val - s.1.start.val)
    (inv := fun s => s.1.end = iter.end ∧
      s.1.start.val ≤ iter.end.val ∧
      s.2.val < 2^(8*s.1.start.val))
  · intro s hs
    rcases s with ⟨iter', v'⟩
    rcases hs with ⟨hend,hbound,hval⟩
    dsimp only [Prod.fst, Prod.snd] at *
    by_cases hstep : iter'.start.val < iter'.end.val
    · have hlt : iter'.end.val ≤ 4 := by simpa [hend] using hb.2
      have hbody := apply_sbox_step_total a v' iter' hstep hlt hval
      step with hbody
      simp only [r_post]
      refine ⟨r_post2.trans hend, ?_, r_post3, ?_⟩
      · have hh := congrArg UScalar.val (r_post2.trans hend)
        have hh1 := congrArg UScalar.val hend
        have hs : it'.start.val = iter'.start.val + 1 := r_post1
        have hlt' : iter'.start.val < iter'.end.val := hstep
        omega
      · have hh := congrArg UScalar.val r_post2
        have hs : it'.start.val = iter'.start.val + 1 := r_post1
        omega
    · have hnone : iter'.end.val ≤ iter'.start.val := by omega
      have hnext := rust_usize_range_next_none iter' hnone
      unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default_loop.body
      step with hnext
      subst o
      simp only [WP.spec_ok]
      have hfinal : iter'.start.val = iter.end.val := by
        have h := congrArg UScalar.val hend
        omega
      simpa [hfinal] using hval
  · exact ⟨rfl, hb.1, hv⟩

/-- The generated RustCrypto Tc26 apply_sbox succeeds on every input. -/
theorem apply_sbox_total (a : Std.U32) :
    tc26SboxExt.apply_sbox a ⦃ _ => True ⦄ := by
  change Magma.Rust.sboxes.SboxExt.apply_sbox.default tc26SboxExt a
    ⦃ _ => True ⦄
  unfold Magma.Rust.sboxes.SboxExt.apply_sbox.default
  step with (apply_sbox_loop_total a 0#u32
    { start := 0#usize, «end» := 4#usize } (by decide) (by decide))

end Magma.Proof

module

public import Magma.Proof.Common.Keys

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow

namespace Magma.Proof

private lemma cloneUsize_exact (x : Std.Usize) : core.clone.CloneUsize.clone x = ok x := by rfl

private lemma ltUsize_exact (x y : Std.Usize) :
    core.cmp.PartialOrdUsize.lt x y = ok (decide (x.val < y.val)) := by rfl

lemma usize_range_next_some (it : core.ops.range.Range Std.Usize) (h : it.start.val < it.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize it ⦃
      (o : Option Std.Usize) (it' : core.ops.range.Range Std.Usize) =>
      o = some it.start ∧ it'.start.val = it.start.val + 1 ∧ it'.end = it.end ⦄ := by
  simpa only [core.iter.range.StepUsize] using
    (core.iter.range.IteratorRange.next_UScalar_some_spec cloneUsize_exact ltUsize_exact it h)

/-- Out-of-range iterator returns none and leaves the range unchanged. -/
lemma usize_range_next_none
    (it : core.ops.range.Range Std.Usize)
    (h : it.end.val ≤ it.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize it
      ⦃ (o : Option Std.Usize) (it' : core.ops.range.Range Std.Usize) =>
        o = none ∧ it' = it ⦄ := by
  simpa only [core.iter.range.StepUsize] using
    (core.iter.range.IteratorRange.next_UScalar_none_spec
      ltUsize_exact it h)

end Magma.Proof

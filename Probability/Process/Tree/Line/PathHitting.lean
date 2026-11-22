/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Line.FirstEntrance
public import Mathlib.Probability.Process.HittingTime

/-!
# First-entrance lines and ordinary path hitting times

## Public declarations

In `ProbabilityTheory.Tree`:

* `firstEntrance_precedes_ray_iff_hittingAfter_le` identifies the event that
  first entrance into `A(ω)` occurs along a fixed path by depth `n` with
  `MeasureTheory.hittingAfter (fun k ω => path(k) ∈ A(ω)) {True} 0 ω ≤ n`.

This uses Mathlib's existing hitting time, including the value `⊤` for paths
that never enter. Its stopping-time theorem is already
`MeasureTheory.Adapted.isStoppingTime_hittingAfter`; no second hitting-time
object or stopping-time proof is introduced here. The line/path connection
is used in J. D. Biggins and A. E. Kyprianou, *Measure change in multitype
branching* (2004), §6, p. 557 and §14, p. 577, Lemmas 6.1 and 14.1,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
This module proves the event identification, not their spine expectation
identity, which additionally requires a branching law and a change of measure.
-/

@[expose] public section

namespace ProbabilityTheory.Tree

open MeasureTheory Combinatorics.UlamHarris

/-- The line's finite-path entrance event is exactly the native hitting-time event. -/
theorem firstEntrance_precedes_ray_iff_hittingAfter_le {Ω Root α : Type*}
    (A : Ω → Set (RootIndexed.TreeNode Root α)) (r : Root) (f : ℕ → α)
    (ω : Ω) (n : ℕ) :
    RootIndexed.Line.Precedes (RootIndexed.Line.firstEntrance (A ω))
      {(r, lineagePrefix f n)} ↔
    hittingAfter (fun k ω => (r, lineagePrefix f k) ∈ A ω) {True} 0 ω ≤ n := by
  have htarget : RootIndexed.Line.Precedes (RootIndexed.Line.firstEntrance (A ω))
      {(r, lineagePrefix f n)} ↔
      RootIndexed.Line.Precedes (A ω) {(r, lineagePrefix f n)} := by
    rw [RootIndexed.Line.precedes_iff_subset_descendantClosure,
      RootIndexed.Line.descendantClosure_firstEntrance,
      RootIndexed.Line.precedes_iff_subset_descendantClosure]
  rw [htarget, RootIndexed.Line.precedes_iff_prefix]
  simp only [Set.mem_singleton_iff, forall_eq, length_lineagePrefix]
  have hh : hittingAfter (fun k ω => (r, lineagePrefix f k) ∈ A ω) {True} 0 ω ≤ n ↔
      ∃ k ≤ n, (r, lineagePrefix f k) ∈ A ω := by
    simpa using (hittingAfter_le_iff
      (u := fun k ω => (r, lineagePrefix f k) ∈ A ω) (s := {True})
      (n := 0) (i := n) (ω := ω))
  rw [hh]
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  have hp := List.prefix_iff_eq_take.mp (lineagePrefix_prefix f hk)
  simpa only [length_lineagePrefix] using (congrArg (fun u => (r, u) ∈ A ω) hp.symm).to_iff

end ProbabilityTheory.Tree

end

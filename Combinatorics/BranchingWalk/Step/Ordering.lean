import Combinatorics.BranchingWalk.Step.Orderable
import Combinatorics.BranchingWalk.Step.PointMeasure

/-!
# Point-measure invariance under child ordering

Ordering changes only slot labels.  Because the relabelling is injective and
covers every surviving raw slot, it preserves the Dirac sum with multiplicity.
-/

open MeasureTheory
open scoped ENNReal

namespace Combinatorics.Branching

/-- Reindexing an orderable step into increasing order preserves its point
measure, including multiplicities. -/
theorem stepPointMeasure_order
    {ι X : Type*} [MeasurableSpace X] [LT ι] [Preorder X]
    (ξ : Step ι X) (h : ξ.IsOrderable) :
    stepPointMeasure (ξ.order h) = stepPointMeasure ξ := by
  classical
  ext s hs
  rw [stepPointMeasure_apply _ s hs, stepPointMeasure_apply _ s hs]
  let f : ι → ℝ≥0∞ := fun j =>
    match ξ j with
    | some x => if x ∈ s then 1 else 0
    | none => 0
  simp only [Step.order]
  change (∑' i, f (ξ.orderingRelabel h i)) = ∑' j, f j
  apply (ξ.orderingRelabel_injective h).tsum_eq
  intro j hj
  have hsurvive : survive ξ j := by
    cases hξ : ξ j with
    | none => simp [f, hξ] at hj
    | some x => exact ⟨x, hξ⟩
  obtain ⟨i, hi⟩ := ξ.orderingRelabel_surjectiveOn_support h hsurvive
  exact ⟨i, hi⟩

end Combinatorics.Branching

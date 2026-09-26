import Combinatorics.BranchingWalk.Cloud.Order.Basic
import Combinatorics.BranchingWalk.Cloud.SliceMeasure

/-!
# Domination order on Dirac sums

`SliceDominates A B` compares two populations as sets, by counting how much of
each lies weakly below every threshold. Read on the Dirac sums of the
populations this is the measure inequality
`μ ((-∞, a]) ≤ ν ((-∞, a])`, which is the form in which the thesis states the
order on finite counting measures.

The two forms agree whenever the slices and the half-lines are measurable;
`sliceDominates_iff_count_restrict` and `cloudDominates_iff_diracSum` record
that equivalence. The `encard` form stays the primitive definition because it
needs no measurable structure at all: a set of positions is a population
whether or not it is measurable.
-/

open MeasureTheory

namespace Combinatorics

namespace Branching

variable {Time X : Type*}

/-- The slice domination order read on counting measures: at every threshold
the first measure has no more mass on the left half-line than the second. -/
def SliceDominatesMeasure [MeasurableSpace X] [Preorder X]
    (μ ν : Measure X) : Prop :=
  ∀ a : X, μ (Set.Iic a) ≤ ν (Set.Iic a)

/-- The set form and the Dirac-sum form of slice domination agree, provided
the two populations and the half-lines are measurable. -/
theorem sliceDominates_iff_count_restrict [MeasurableSpace X] [Preorder X]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hIic : ∀ a : X, MeasurableSet (Set.Iic a)) :
    SliceDominates A B ↔
      SliceDominatesMeasure (Measure.count.restrict A) (Measure.count.restrict B) := by
  simp only [SliceDominates, SliceDominatesMeasure]
  refine forall_congr' fun a => ?_
  rw [Measure.count_restrict_apply A (hIic a) ((hIic a).inter hA),
    Measure.count_restrict_apply B (hIic a) ((hIic a).inter hB),
    Set.inter_comm (Set.Iic a) A, Set.inter_comm (Set.Iic a) B]
  exact ENat.toENNReal_le.symm

namespace CloudSet

/-- The cloud domination order read on Dirac sums: slicewise domination of the
time-indexed counting measures. -/
def DominatesMeasure [MeasurableSpace X] [Preorder X]
    (μ ν : Time → Measure X) : Prop :=
  ∀ t : Time, SliceDominatesMeasure (μ t) (ν t)

/-- The cloud order and the order on the cloud Dirac sums agree whenever every
time slice and every half-line is measurable. -/
theorem dominates_iff_diracSum [MeasurableSpace X] [Preorder X]
    {C D : CloudSet Time X} (hC : ∀ t : Time, MeasurableSet (C.points t))
    (hD : ∀ t : Time, MeasurableSet (D.points t))
    (hIic : ∀ a : X, MeasurableSet (Set.Iic a)) :
    C.Dominates D ↔ DominatesMeasure C.diracSum D.diracSum := by
  simp only [CloudSet.Dominates, DominatesMeasure]
  exact forall_congr' fun t =>
    sliceDominates_iff_count_restrict (hC t) (hD t) hIic

end CloudSet

end Branching

end Combinatorics

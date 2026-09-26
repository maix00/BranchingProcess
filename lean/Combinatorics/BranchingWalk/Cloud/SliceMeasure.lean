import Combinatorics.BranchingWalk.Cloud.Basic
import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a cloud

A cloud is a family of spatial point sets indexed by time. Its Dirac sum is
the time-indexed family of counting measures of those slices: at time `t` it
is `∑_{x ∈ C.points t} δ_x`. Mathlib's counting measure is defined as
`Measure.sum Measure.dirac`, so the slice measure is
`Measure.count.restrict (C.points t)`; `Measure.count_apply` then identifies
its value on a measurable set with the cardinality `encard` of the slice
intersected with that set.
-/

open MeasureTheory

namespace Combinatorics

namespace Branching

namespace Cloud

variable {Time X : Type*}

/-- The Dirac sum of a cloud: at each time, the counting measure on the
particles survive at that time. -/
noncomputable def diracSum [MeasurableSpace X] (C : Cloud Time X) :
    Time → Measure X :=
  fun t => Measure.count.restrict (C.points t)

/-- The value of the slice Dirac sum on a measurable set. -/
theorem diracSum_apply [MeasurableSpace X] (C : Cloud Time X) (t : Time)
    {s : Set X} (hs : MeasurableSet s) :
    C.diracSum t s = Measure.count (s ∩ C.points t) :=
  Measure.restrict_apply hs

/-- On a half-line, the slice Dirac sum is the cardinality of the slice inside
that half-line. This is the measure-level form of `SliceDominates`. -/
theorem diracSum_Iic_eq_encard [MeasurableSpace X] [Preorder X]
    (C : Cloud Time X) (t : Time) (a : X)
    (ha : MeasurableSet (Set.Iic a)) (hC : MeasurableSet (C.points t)) :
    C.diracSum t (Set.Iic a) = (C.points t ∩ Set.Iic a).encard := by
  rw [diracSum, Measure.count_restrict_apply (C.points t) ha (ha.inter hC),
    Set.inter_comm]

end Cloud

end Branching

end Combinatorics

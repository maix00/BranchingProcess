import Probability.BranchingRandomWalk.Assumptions.Moments
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.SlotOrder

/-!
# Named assumption bundles for the thesis theorems

Bundles record the statements currently used by each main theorem. Keeping
the component predicates public lets intermediate lemmas request a smaller
set of hypotheses.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



structure BasicBranchingAssumptions {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  nonempty : HasAtLeastOneChild L.raw
  supercritical : IsSupercriticalBranchingLaw L.raw
  normalized : HasBoundaryNormalization L.potential L.raw

/-- Moment assumptions survively stated for Theorem 1.1 when `a > 0`.
The centered-spine and finite-variance fields will be added with the
measure-theoretic spine law, rather than duplicated as raw slot formulas. -/
structure TrajectoryMomentAssumptions {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  cross : HasFiniteCrossWeight L.potential L.raw
  first : HasLeftmostFirstMoment L
  fourth : HasLeftmostFourthMoment L

/-- The extra hypothesis survively used for the `a = 0` trajectory argument. -/
structure RestartMomentAssumption {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  exponential : HasLeftmostPositiveExponentialMoment L

/-- The intended moment layer for the one-sided Theorem 1.3 proof. -/
structure SpeedL1MomentAssumption {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  first : HasLeftmostFirstMoment L

end ProbabilityTheory.BranchingRandomWalk

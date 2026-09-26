import Probability.BranchingRandomWalk.Assumptions.Moments
import Combinatorics.BranchingWalk.Step.Measurability

/-!
# Named assumption bundles for the thesis theorems

Bundles record the statements currently used by each main theorem. Keeping
the component predicates public lets intermediate lemmas request a smaller
set of hypotheses.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



structure BasicBranchingAssumptions (μ : Measure NatRealStep) : Prop where
  ordered : HasOrderedSlots μ
  nonempty : HasAtLeastOneChild μ
  supercritical : IsSupercriticalBranchingLaw μ
  normalized : HasBoundaryNormalization μ

/-- Moment assumptions survively stated for Theorem 1.1 when `a > 0`.
The centered-spine and finite-variance fields will be added with the
measure-theoretic spine law, rather than duplicated as raw slot formulas. -/
structure TrajectoryMomentAssumptions (μ : Measure NatRealStep) : Prop where
  cross : HasFiniteCrossWeight μ
  first : HasLeftmostFirstMoment μ
  fourth : HasLeftmostFourthMoment μ

/-- The extra hypothesis survively used for the `a = 0` trajectory argument. -/
structure RestartMomentAssumption (μ : Measure NatRealStep) : Prop where
  exponential : HasLeftmostPositiveExponentialMoment μ

/-- The intended moment layer for the one-sided Theorem 1.3 proof. -/
structure SpeedL1MomentAssumption (μ : Measure NatRealStep) : Prop where
  first : HasLeftmostFirstMoment μ

end ProbabilityTheory.BranchingRandomWalk

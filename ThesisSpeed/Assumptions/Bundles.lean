import ThesisSpeed.Assumptions.Moments

/-!
# Named assumption bundles for the thesis theorems

Bundles record the statements currently used by each main theorem. Keeping
the component predicates public lets intermediate lemmas request a smaller
set of hypotheses.
-/

open MeasureTheory

namespace ThesisSpeed

structure BasicBranchingAssumptions (μ : Measure NatRealBranchingStep) : Prop where
  ordered : HasOrderedSlots μ
  nonempty : HasAtLeastOneChild μ
  supercritical : IsSupercriticalBranchingLaw μ
  normalized : HasBoundaryNormalization μ

/-- Moment assumptions presently stated for Theorem 1.1 when `a > 0`.
The centered-spine and finite-variance fields will be added with the
measure-theoretic spine law, rather than duplicated as raw slot formulas. -/
structure TrajectoryMomentAssumptions (μ : Measure NatRealBranchingStep) : Prop where
  cross : HasFiniteCrossWeight μ
  first : HasLeftmostFirstMoment μ
  fourth : HasLeftmostFourthMoment μ

/-- The extra hypothesis presently used for the `a = 0` trajectory argument. -/
structure RestartMomentAssumption (μ : Measure NatRealBranchingStep) : Prop where
  exponential : HasLeftmostPositiveExponentialMoment μ

/-- The intended moment layer for the one-sided Theorem 1.3 proof. -/
structure SpeedL1MomentAssumption (μ : Measure NatRealBranchingStep) : Prop where
  first : HasLeftmostFirstMoment μ

end ThesisSpeed

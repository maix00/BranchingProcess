import Probability.Distributions.Stable.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The reverse characterization returns a genuinely nondegenerate Gaussian. -/
example {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsStrictlyAlphaStable 2 μ) :
    ∃ v : ℝ≥0, v ≠ 0 ∧ μ = gaussianReal 0 v :=
  h.exists_gaussianReal_zero

#print axioms ProbabilityTheory.IsStrictlyAlphaStable.exists_gaussianReal_zero

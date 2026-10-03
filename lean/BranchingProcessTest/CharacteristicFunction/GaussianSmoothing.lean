import Probability.Distributions.CharacteristicFunction.GaussianSmoothing

open MeasureTheory ProbabilityTheory

example (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
      (1 - ‖charFun μ (2 * Real.pi * u * s)‖ ^ 2)) =
      ∫ x : ℝ, 1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2)
        ∂symmetrizedMeasure μ :=
  integral_gaussian_normCharFunDefect_eq_laplaceDefect μ u

#print axioms ProbabilityTheory.charFun_symmetrizedMeasure
#print axioms ProbabilityTheory.charFun_symmetrizedMeasure_re
#print axioms ProbabilityTheory.integral_gaussian_charFunDefect_eq_laplaceDefect
#print axioms ProbabilityTheory.integral_gaussian_normCharFunDefect_eq_laplaceDefect

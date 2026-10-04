import Analysis.Fourier.Bochner

open MeasureTheory ProbabilityTheory

example (φ : ℝ → ℂ) (hφc : Continuous φ) (hpd : IsPositiveDefinite φ)
    (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ ξ, charFun (μ : Measure ℝ) ξ = φ ξ :=
  bochner φ hφc hpd h0

#print axioms ProbabilityTheory.bochner

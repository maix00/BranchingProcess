import MeasureTheory.Measure.CharacteristicFunction.ProbabilityMeasure

open MeasureTheory Complex ComplexConjugate

example (μ : ProbabilityMeasure ℝ) {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun (μ : Measure ℝ) (ξ i - ξ j)).re :=
  MeasureTheory.ProbabilityMeasure.charFun_positiveSemiDefinite μ ξ c

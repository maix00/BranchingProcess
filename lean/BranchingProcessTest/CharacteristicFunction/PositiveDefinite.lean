import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite

open MeasureTheory ProbabilityTheory Complex ComplexConjugate

example (μ : ProbabilityMeasure ℝ) {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun (μ : Measure ℝ) (ξ i - ξ j) =
      ∫ a : ℝ,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ)
        ∂(μ : Measure ℝ) :=
  MeasureTheory.ProbabilityMeasure.charFun_sum_eq_integral_normSq μ ξ c

example (μ : ProbabilityMeasure ℝ) :
    IsPositiveDefinite (fun ξ => charFun (μ : Measure ℝ) ξ) :=
  IsPositiveDefinite.of_charFun μ

example (x : ℝ) :
    IsPositiveDefinite (fun ξ => charFun (Measure.dirac x) ξ) := by
  exact IsPositiveDefinite.of_charFun
    ⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩

example (x ξ : ℝ) :
    charFun (Measure.dirac x) ξ = Complex.exp ((ξ : ℂ) * (x : ℂ) * I) := by
  simp

#print axioms MeasureTheory.ProbabilityMeasure.charFun_sum_eq_integral_normSq
#print axioms MeasureTheory.ProbabilityMeasure.charFun_positiveSemiDefinite
#print axioms ProbabilityTheory.IsPositiveDefinite.of_charFun

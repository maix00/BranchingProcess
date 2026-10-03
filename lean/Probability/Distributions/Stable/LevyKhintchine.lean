import Probability.Distributions.Stable.Convolution
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Uniqueness

/-!
# Lévy–Khintchine representation of a strictly stable law

This file applies the measure-level Lévy–Khintchine theorem to strictly stable
laws.
-/

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure

/-- A strictly stable law is infinitely divisible. -/
theorem IsStrictlyAlphaStable.isInfinitelyDivisible
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    IsInfinitelyDivisible μ := by
  intro n hn
  obtain ⟨ν, hν, hpower⟩ := h.exists_convPower_root n hn
  exact ⟨ν, hν, hpower⟩

/-- The real stable law has a unique Lévy–Khintchine triple. -/
theorem IsStrictlyAlphaStable.existsUnique_levyKhintchineTriple
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    ∃! T : LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  exact ProbabilityTheory.existsUnique_levyKhintchineTriple
    h.isInfinitelyDivisible

end ProbabilityTheory

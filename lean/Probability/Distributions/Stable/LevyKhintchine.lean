import Probability.Distributions.Stable.Convolution
import LeanLevy.Levy.LevyKhintchineUniqueness

/-!
# Lévy–Khintchine representation of a strictly stable law

This file connects the project's convolution-power definition to the vendored
measure-level Lévy–Khintchine theorem.
-/

namespace MeasureTheory.Measure

/-- The two independently introduced natural-number convolution powers agree. -/
theorem convPower_eq_iteratedConv {E : Type*} [AddCommMonoid E]
    [MeasurableSpace E] (μ : Measure E) (n : ℕ) :
    μ.convPower n = μ.iteratedConv n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [convPower_succ, iteratedConv_succ, ih]

end MeasureTheory.Measure

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure

/-- A strictly stable law is infinitely divisible. -/
theorem IsStrictlyAlphaStable.isInfinitelyDivisible
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    IsInfinitelyDivisible μ := by
  intro n hn
  obtain ⟨ν, hν, hpower⟩ := h.exists_convPower_root n hn
  exact ⟨ν, hν, hpower.trans (Measure.convPower_eq_iteratedConv ν n)⟩

/-- The real stable law has a unique Lévy–Khintchine triple. -/
theorem IsStrictlyAlphaStable.existsUnique_levyKhintchineTriple
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    ∃! T : LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  exact ProbabilityTheory.existsUnique_levyKhintchineTriple
    h.isInfinitelyDivisible

end ProbabilityTheory

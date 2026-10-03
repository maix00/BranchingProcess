module

public import MeasureTheory.Integral.Lebesgue.RestrictLimit
public import Probability.Process.Levy.Jump.SmallVariation

/-!
# Vanishing variation on shrinking jump bands

This module applies the general restricted-integral limit to Poisson jump
variation.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped Topology

/-- Campbell's expectation identity turns finite-variation truncation into a
positive-probability small-residual event at some deterministic cutoff. -/
theorem exists_smallVariation_pos_of_campbell
    {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω]
    (ν : Measure E) (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : E → ENNReal) (band : ℕ → Set E) (V : ℕ → Ω → ENNReal)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ν) ≠ ⊤)
    (haway : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∉ band n)
    (hV : ∀ n, Measurable (V n))
    (hcampbell : ∀ n, (∫⁻ ω, V n ω ∂P) =
      ∫⁻ x in band n, weight x ∂ν)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < P {ω | V n ω < ENNReal.ofReal ρ} := by
  obtain ⟨n, hn⟩ := MeasureTheory.exists_lintegral_restrict_lt_of_eventually_not_mem
    ν weight band hweight hband hfinite haway ρ hρ
  exact ⟨n, measure_smallVariation_pos P (V n) (hV n)
    (ENNReal.ofReal ρ) (by simpa [hcampbell n] using hn)⟩

end ProbabilityTheory

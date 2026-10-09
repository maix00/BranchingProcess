/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Campbell
import Probability.MeasureTheory.SmallValue.RestrictedIntegral

/-!
# Small Poisson integrals on shrinking mark regions

Campbell's identity and a finite first moment give a deterministic cutoff
whose realized Poisson integral is small with positive probability.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open Filter

/-- The Campbell identity and finite first jump moment give a deterministic
cutoff whose realized small-jump variation is small with positive probability. -/
theorem exists_poissonSmallVariation_pos
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂m) ≠ ⊤)
    (haway : ∀ᵐ x ∂m, ∀ᶠ n in atTop, x ∉ band n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < P {ω | (∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω)) <
      ENNReal.ofReal ρ} := by
  apply exists_smallVariation_pos_of_campbell m P weight band
    (fun n ω => ∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω))
    hweight hband hfinite haway
  · intro n
    have hm := measurable_lintegral_poissonRandomMeasure
      hd.measurable_count hd.measurable_point (hweight.indicator (hband n))
    simpa only [lintegral_indicator (hband n)] using hm
  · intro n
    exact lintegral_poissonRandomMeasure_restrict hd (band n) (hband n) weight hweight
  · exact hρ

end ProbabilityTheory

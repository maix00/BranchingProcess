/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Basic

/-!
# Campbell's identity on a measurable region

The expected Poisson random-measure integral over a measurable region is the
corresponding integral against the intensity measure.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- Restricting a Poisson random-measure integral to a measurable region
restricts the intensity integral by the same region. -/
theorem lintegral_poissonRandomMeasure_restrict
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    (A : Set E) (hA : MeasurableSet A)
    (weight : E → ENNReal) (hweight : Measurable weight) :
    (∫⁻ ω, ∫⁻ x in A, weight x ∂(poissonRandomMeasure K X ω) ∂P) =
      ∫⁻ x in A, weight x ∂m := by
  have h := lintegral_lintegral_poissonRandomMeasure hd (hweight.indicator hA)
  simpa only [lintegral_indicator hA] using h

end ProbabilityTheory

end

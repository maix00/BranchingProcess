/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.RandomMeasure.Evaluation

import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Campbell's identity on a measurable region

The expected Poisson random-measure integral over a measurable region is the
corresponding integral against the intensity measure.

## Public declarations

- `bind_poissonRandomMeasure_eq_intensity` identifies the average random measure with $m$.
- `lintegral_lintegral_poissonRandomMeasure` is Campbell's formula:
  $\mathbb E[\int g\,dN]=\int g\,dm$ for measurable nonnegative $g$.
- `lintegral_poissonRandomMeasure_restrict` gives Campbell's formula on a measurable region.

The expectation identity is the intensity-measure form of Campbell's formula;
see Proposition 2.7, Section 2.2, pages 12--13, of Günter Last and Mathew
Penrose, *Lectures on the Poisson Process*, Institute of Mathematical
Statistics Textbooks, Cambridge University Press, 2017,
DOI 10.1017/9781316104477.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped ENNReal

section CampbellFormula

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m]
    [Nonempty E] {μ : Measure Ω}

/-- The average of the Poisson random measure is its intensity measure. -/
theorem bind_poissonRandomMeasure_eq_intensity [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) :
    μ.bind (poissonRandomMeasure K X) = m := by
  ext A hA
  rw [Measure.bind_apply hA
    (measurable_poissonRandomMeasure hd.measurable_count hd.measurable_point).aemeasurable]
  exact lintegral_poissonRandomMeasure_apply hd hA

/-- **Campbell's formula** (Lebesgue form): the mean of `∫⁻ g dN` over `ω` is `∫⁻ g dm`. -/
theorem lintegral_lintegral_poissonRandomMeasure [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {g : E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂(poissonRandomMeasure K X ω) ∂μ = ∫⁻ x, g x ∂m := by
  calc
    ∫⁻ ω, ∫⁻ x, g x ∂(poissonRandomMeasure K X ω) ∂μ
      = ∫⁻ x, g x ∂(μ.bind (poissonRandomMeasure K X)) :=
        (Measure.lintegral_bind
          (measurable_poissonRandomMeasure hd.measurable_count hd.measurable_point).aemeasurable
          hg.aemeasurable).symm
    _ = ∫⁻ x, g x ∂m := by rw [bind_poissonRandomMeasure_eq_intensity hd]


end CampbellFormula

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

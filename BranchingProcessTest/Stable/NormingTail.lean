/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Distributions.Stable.Attraction.Norming.Tail
import Probability.Distributions.Stable.Attraction.Norming.UniformTail
import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian

/-!
# Stable norming tail API checks

The examples compose the domain-of-attraction tail theorem with stable
norming to obtain scale-level tail and truncated-moment limits.
-/

open Filter MeasureTheory ProbabilityTheory

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit) {normalization center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure normalization center)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ν.real {x : ℝ | normalization n < |x|}) atTop
      (nhds ((2 - α) / α)) := by
  exact hnorm.tendsto_nat_mul_twoSidedTail_of_regularlyVarying hα₀ hα₂
    (h.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂)

example {α c : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      truncatedSecondMoment ν (c * normalization n) / normalization n ^ 2)
      atTop (nhds (c ^ (2 - α))) :=
  hnorm.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq
    hα₀ hα₂ htail hc

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit) {normalization center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure normalization center)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn
      (fun (n : ℕ) (c : ℝ) => (n : ℝ) *
        ν.real {x : ℝ | c * normalization n < |x|})
      (fun c => ((2 - α) / α) * c ^ (-α)) atTop (Set.Icc a b) := by
  exact hnorm.tendstoUniformlyOn_nat_mul_twoSidedTail_mul_of_regularlyVarying
    hα₀ hα₂ (h.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂) ha hab

#print axioms ProbabilityTheory.IsStableNorming.tendsto_nat_mul_twoSidedTail_of_regularlyVarying
#print axioms ProbabilityTheory.IsStableNorming.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
#print axioms ProbabilityTheory.IsStableNorming.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq
#print axioms ProbabilityTheory.IsStableNorming.tendstoUniformlyOn_nat_mul_twoSidedTail_mul_of_regularlyVarying

import Probability.Distributions.Stable.Attraction.NormingRatios.Tauberian

/-! Public API checks for the inverse Tauberian chain from stable attraction
to tails and truncated second moments. Intermediate positivity, Potter
bounds, and the Mellin limit are proved internally, not supplied by callers. -/

open Filter MeasureTheory
open scoped Topology

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hstable : ProbabilityTheory.IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @ProbabilityTheory.IsInDomainOfAttractionAlong ν limit inferInstance
      hstable.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun x : ℝ => ν.real {y : ℝ | x < |y|}) (-α) :=
  h.isRegularlyVarying_twoSidedTail hstable hα₀ hα₂

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hstable : ProbabilityTheory.IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @ProbabilityTheory.IsInDomainOfAttractionAlong ν limit inferInstance
      hstable.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto
      (fun x : ℝ => ProbabilityTheory.truncatedSecondMoment ν x /
        (x ^ 2 * (1 - ‖charFun ν x⁻¹‖ ^ 2)))
      atTop
      (nhds (1 / (2 * (2 - α) *
        Analysis.Fourier.CosineTauberian.cosineTauberianCosineMoment α))) :=
  h.tendsto_truncatedSecondMoment_div_scaledCosineDefect
    hstable hα₀ hα₂

#print axioms ProbabilityTheory.twoSidedTail_div_symmetrized_tendsto_half
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedCosineDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.exists_potter_bound_symmetrizedCosineDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.exists_potter_envelope_symmetrizedCosineDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_secondTailIntegral_ratio
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedTwoSidedTail
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.isRegularlyVarying_twoSidedTail
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.isSlowlyVarying_stableSlowVariation
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_symmetrizedTail_div_cosineDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_twoSidedTail_div_cosineDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_truncatedSecondMoment_div_scaledCosineDefect

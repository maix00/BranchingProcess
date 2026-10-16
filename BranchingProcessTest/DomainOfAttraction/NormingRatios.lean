import MeasureTheory.Measure.CharacteristicFunction.Convergence
import Probability.Distributions.Stable.Attraction.NormingRatios.RegularVariation

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

example {μ : ℕ → Measure ℝ} {μLimit : Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure μLimit]
    {K : Set ℝ} (hK : IsCompact K)
    (hcf : ∀ t : ℝ, Tendsto (fun n => charFun (μ n) t) atTop
      (nhds (charFun μLimit t))) :
    TendstoUniformlyOn (fun n t => charFun (μ n) t) (charFun μLimit) atTop K :=
  MeasureTheory.tendstoUniformlyOn_charFun_of_tendsto hK hcf

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hstable : IsAlphaStable α limit) {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hstable.isProbabilityMeasure scale center)
    (m : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / (n : ℝ)) atTop (nhds r)) :
    Tendsto (fun n : ℕ => scale (m n) / scale n) atTop
      (nhds (Real.rpow r α⁻¹)) :=
  h.tendsto_norming_ratio hstable m r hr hm

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hstable : IsAlphaStable α limit) {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hstable.isProbabilityMeasure scale center)
    (s : ℝ) (hs : 0 < s) :
    Tendsto
      (fun u : ℝ =>
        (1 - ‖charFun ν (s * u)‖ ^ 2) /
          (1 - ‖charFun ν u‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (nhds (s ^ α)) :=
  h.tendsto_normDefect_ratio_nhdsGT_zero hstable s hs

#print axioms MeasureTheory.tendstoUniformlyOn_charFun_of_tendsto
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_norming_ratio
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_norming_succ_ratio
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_scale_atTop
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.exists_tendstoUniformlyOn_normDefect
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_normDefect_ratio_nhdsGT_zero

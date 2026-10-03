import Probability.Distributions.Stable.Attraction.CharacteristicFunction

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

example (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    charFun ((iidSequenceLaw ν).map
      (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k)) =
      fun t => (charFun ν t) ^ n :=
  iidSequenceLaw_charFun_sum n

example {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto
      (fun n => (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I))
      atTop (nhds (charFun limit t)) :=
  h.tendsto_charFun_normalizedIidSum t

example {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto (fun n => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n)
      atTop (nhds ‖charFun limit t‖) :=
  h.tendsto_norm_charFun_oneStep_pow t

example {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, ‖charFun μ t‖ = Real.exp (-c * |t| ^ α) :=
  h.exists_pos_norm_charFun_eq_exp

example {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hstable : IsAlphaStable α limit) {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hstable.isProbabilityMeasure scale center) :
    ∃ c : ℝ, 0 < c ∧
      (∀ t : ℝ, Tendsto
        (fun n : ℕ => (n : ℝ) *
          (-Real.log ‖charFun ν ((scale n)⁻¹ * t)‖))
        atTop (nhds (c * |t| ^ α))) ∧
      (∀ t : ℝ, Tendsto
        (fun n : ℕ => (n : ℝ) *
          (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2))
        atTop (nhds (2 * c * |t| ^ α))) :=
  h.exists_pos_tendsto_log_norm_charFun_and_norm_defect hstable

#print axioms ProbabilityTheory.iidSequenceLaw_charFun_sum
#print axioms ProbabilityTheory.charFun_map_normalizedIidSum
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_charFun_normalizedIidSum
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_norm_charFun_oneStep_pow
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.exists_pos_tendsto_log_norm_charFun_and_norm_defect

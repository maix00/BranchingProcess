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

#print axioms ProbabilityTheory.iidSequenceLaw_charFun_sum
#print axioms ProbabilityTheory.charFun_map_normalizedIidSum
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_charFun_normalizedIidSum
#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.tendsto_norm_charFun_oneStep_pow

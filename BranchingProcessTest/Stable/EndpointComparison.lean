import Probability.Process.Stable.SmallDeviation.EndpointComparison

open MeasureTheory Filter
open scoped NNReal Topology

#check
  ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_corridor_div_endpointCorridor_of_cdf
#check
  ProbabilityTheory.IsStableLevyProcess.eventually_centeredCorridorProbability_le_endpointCorridor_mul_of_cdf

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧ ProbabilityTheory.cdf μ 0 < 1)
    (c b ε δ : ℝ) (hc : -1 ≤ c) (hcb : c < b) (hb : b ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤ Real.log
        ((ProbabilityTheory.centeredCorridorProbability P X a).toReal) /
        Real.log ((P (ProbabilityTheory.fullSegmentCorridorIocReturnEvent
          X 0 1 (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))).toReal) := by
  exact h.eventually_one_sub_le_log_corridor_div_endpointCorridor_of_cdf
    hcdf c b ε δ hc hcb hb hε hδ

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (hcdf : 0 < ProbabilityTheory.cdf μ 0 ∧ ProbabilityTheory.cdf μ 0 < 1)
    (c b ε : ℝ) (hc : -1 ≤ c) (hcb : c < b) (hb : b ≤ 1)
    (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (ProbabilityTheory.centeredCorridorProbability P X a).toReal ≤
          D * (P (ProbabilityTheory.fullSegmentCorridorIocReturnEvent
            X 0 1 (-(1 + ε) * a) ((1 + ε) * a) (a * c) (a * b))).toReal := by
  exact h.eventually_centeredCorridorProbability_le_endpointCorridor_mul_of_cdf
    hcdf c b ε hc hcb hb hε

#print axioms ProbabilityTheory.IsStableLevyProcess.eventually_one_sub_le_log_corridor_div_endpointCorridor_of_cdf
#print axioms
  ProbabilityTheory.IsStableLevyProcess.eventually_centeredCorridorProbability_le_endpointCorridor_mul_of_cdf

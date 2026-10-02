import Probability.Process.Stable.SmallDeviation.BlockBounds
import Probability.Process.Stable.SmallDeviation.Blocks.Upper.ArbitraryHorizon

open MeasureTheory
open scoped NNReal ENNReal

#check ProbabilityTheory.IsStableLevyProcess.measure_rationalTube_le_pow_floor_inv_horizon
#check ProbabilityTheory.IsStableLevyProcess.measure_fullCorridor_le_pow_floor_inv_horizon
#check
  ProbabilityTheory.IsStableLevyProcess.iInf_sevenBlockEndpointProbability_pow_le_corridor_of_horizon

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (hc1 : c ≤ 1) :
    P (ProbabilityTheory.fullSegmentCorridorEvent X 0 1 (-a) a) ≤
      (P (ProbabilityTheory.rationalHorizonTubeEvent X
        ⟨c, hc.le⟩ (2 * a))) ^ ⌊c⁻¹⌋₊ :=
  h.measure_fullCorridor_le_pow_floor_inv_horizon a c ha hc hc1

example {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : ProbabilityTheory.IsStableLevyProcess α μ X P)
    (a ε c : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    (⨅ i : Fin 7, P (ProbabilityTheory.fullSegmentCorridorIocReturnEvent X 0
      ⟨c, hc.le⟩ (-a) a
      ((ProbabilityTheory.blockEndpointShift i - 1) * ε * a)
      ((ProbabilityTheory.blockEndpointShift i + 1) * ε * a))) ^
        (⌊c⁻¹⌋₊ + 1) ≤
      P (ProbabilityTheory.fullSegmentCorridorEvent X 0 1
        (-(a * (1 + 4 * ε))) (a * (1 + 4 * ε))) :=
  h.iInf_sevenBlockEndpointProbability_pow_le_corridor_of_horizon
    a ε c ha hε hc hc1

#print axioms ProbabilityTheory.IsStableLevyProcess.measure_rationalTube_le_pow_floor_inv_horizon
#print axioms ProbabilityTheory.IsStableLevyProcess.measure_fullCorridor_le_pow_floor_inv_horizon
#print axioms ProbabilityTheory.IsStableLevyProcess.iInf_sevenBlockEndpointProbability_pow_le_corridor_of_horizon

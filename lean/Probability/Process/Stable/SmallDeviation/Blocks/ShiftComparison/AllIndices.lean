import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Core
import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Support
import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Feedback
import Probability.Process.Stable.SmallDeviation.ShiftedCorridor
import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.PoissonEntrance
import Probability.Distributions.Stable.Sign

/-!
# Stable corridor comparison across indices

The entrance and logarithmic comparison results under the source CDF
condition, with the index ranges assembled from their respective proofs.
-/

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The unit-time entrance event is positive under the source CDF condition
for every strictly stable index. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  rcases lt_trichotomy α 1 with hα | hα | hα
  · exact h.measure_fullEntrance_pos_indexLTOne hα hcdf b c ε hb hc hε
  · subst α
    exact h.measure_fullEntrance_pos_indexOne b c ε hb hc hε
  · exact h.measure_fullEntrance_pos_of_cdfAtZero hα hcdf b c ε hb hc hε

/-- The source's left-open, right-closed endpoint event is positive under
the source CDF condition for every strictly stable index. -/
theorem IsStableLevyProcess.measure_sourceEntrance_pos_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorEvent X 0 1 (c - 1) (c + 1) ∩
      {ω | c - b - ε < segmentIncrement X 0 1 ω ⊤ ∧
        segmentIncrement X 0 1 ω ⊤ ≤ c - b + ε}) := by
  rcases lt_trichotomy α 1 with hα | hα | hα
  · exact h.measure_sourceEntrance_pos_indexLTOne hα hcdf b c ε hb hc hε
  · subst α
    exact h.measure_sourceEntrance_pos_indexOne b c ε hb hc hε
  · exact h.measure_sourceEntrance_pos_of_cdfAtZero hα hcdf b c ε hb hc hε

/-- The scaled entrance probability used in the proof of (21) is exactly
constant near zero under stable time-space scaling, and its source-event
value is positive. -/
theorem IsStableLevyProcess.tendsto_measure_scaledEntrance_corridorReturn_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    Filter.Tendsto
      (fun a : ℝ => P (fullSegmentCorridorReturnEvent X 0
        (stableEntranceHorizon α a)
        (a * (c - 1)) (a * (c + 1))
        (a * (c - b - ε)) (a * (c - b + ε))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (P (fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)))) ∧
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  have hp := h.measure_fullEntrance_pos_of_cdfAtZero_allIndices
    hcdf b c ε hb hc hε
  let p := P (fullSegmentCorridorReturnEvent X 0 1
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))
  have heq : (fun a : ℝ => P (fullSegmentCorridorReturnEvent X 0
      (stableEntranceHorizon α a)
      (a * (c - 1)) (a * (c + 1))
      (a * (c - b - ε)) (a * (c - b + ε)))) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] fun _ => p := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    dsimp [p]
    exact h.shortEntrance_fullCorridorReturn_probability a ha
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)
  constructor
  · exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · exact hp

/-- The entrance-probability limit used in relation (21), with the source's
exact `Ioc` endpoint convention: the
scaled probability is constant for positive scales and the limiting value is
strictly positive under the CDF condition. -/
theorem IsStableLevyProcess.tendsto_measure_scaledSourceEntrance_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    Filter.Tendsto
      (fun a : ℝ => P (fullSegmentCorridorIocReturnEvent X 0
        (stableEntranceHorizon α a)
        (a * (c - 1)) (a * (c + 1))
        (a * (c - b - ε)) (a * (c - b + ε))))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (P (fullSegmentCorridorIocReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε)))) ∧
    0 < P (fullSegmentCorridorIocReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  have hp : 0 < P (fullSegmentCorridorIocReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
    simpa [fullSegmentCorridorIocReturnEvent,
      segmentCorridorEndpointEvent, Set.mem_Ioc] using
      h.measure_sourceEntrance_pos_of_cdfAtZero_allIndices
        hcdf b c ε hb hc hε
  let p := P (fullSegmentCorridorIocReturnEvent X 0 1
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))
  have heq : (fun a : ℝ => P (fullSegmentCorridorIocReturnEvent X 0
      (stableEntranceHorizon α a)
      (a * (c - 1)) (a * (c + 1))
      (a * (c - b - ε)) (a * (c - b + ε)))) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] fun _ => p := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    dsimp [p]
    exact h.shortEntrance_fullSegmentCorridorIocReturn_probability a ha
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)
  constructor
  · exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · exact hp

end ProbabilityTheory

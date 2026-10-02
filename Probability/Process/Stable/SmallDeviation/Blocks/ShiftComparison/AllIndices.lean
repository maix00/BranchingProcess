import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison
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
    simpa [fullSegmentCorridorIocReturnEvent] using
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

/-- Lemma 2(a), relation (21), in its eventual-ratio formulation: for every
`δ > 0`, the ratio of the two negative logarithms is eventually at least
`1 - δ`. This is the `liminf ≥ 1` conclusion in the source's convention for
comparing negative functions, uniformly over all strictly stable indices. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  rcases lt_trichotomy α 1 with hα | hα | hα
  · exact h.eventually_one_sub_le_logCorridor_ratio_indexLTOne
      hα hcdf b c ε hb hc hε δ hδ
  · subst α
    exact h.eventually_one_sub_le_logCorridor_ratio_indexOne
      b c ε hb hc hε δ hδ
  · exact h.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero
      hα hcdf b c ε hb hc hε δ hδ

/-- Lemma 2(a), relation (21), under the source's strict distribution
function convention `F(0) = μ((-∞, 0))`. The proof converts that condition to
Mathlib's right-continuous CDF convention using strict stability, then applies
the all-index comparison theorem. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_strictLeftMass_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  exact h.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero_allIndices
    (h.increments.strictlyStable.cdfAtZero_condition_of_strictLeftMass hleft)
    b c ε hb hc hε δ hδ

end ProbabilityTheory

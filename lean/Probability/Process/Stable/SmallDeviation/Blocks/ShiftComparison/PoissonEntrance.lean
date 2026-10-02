import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison
import Probability.Process.Stable.JumpModel.EntranceLaw
import Probability.Distributions.Stable.LevyKhintchine

/-!
# Poisson entrance input for the shifted-corridor comparison

The finite-variation jump model supplies the fixed entrance probability for
stable index below one. This file connects that path construction to the
comparison theorem without changing the module status of either API layer.
-/

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- For stable index below one, the finite-variation Poisson jump model
supplies the entrance probability needed in the shifted-corridor comparison.
This proves the ratio conclusion under the original CDF sign condition. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero_of_poissonModel
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
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
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  have hp := h.measure_fullEntrance_pos_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε
  exact h.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    hpos hneg b c ε hb hε.le hp δ hδ

/-- The probability in relation (21) is constant under the stable
time-space scaling, and its unit-time value is strictly positive for
`α < 1` under the source CDF hypothesis. In particular, the corresponding
liminf equals this positive unit-time probability. -/
theorem IsStableLevyProcess.tendsto_measure_scaledEntrance_corridorReturn_of_cdfAtZero_of_poissonModel
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (T : LevyKhintchineTriple) [SigmaFinite T.levyMeasure]
    (hT : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ))
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
  let p := P (fullSegmentCorridorReturnEvent X 0 1
    (c - 1) (c + 1) (c - b - ε) (c - b + ε))
  have hp : 0 < p := h.measure_fullEntrance_pos_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε
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

/-- The strict stable-law assumption supplies the Lévy--Khintchine triple
internally, so the entrance conclusion does not expose that representation to
callers. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_indexLTOne
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  obtain ⟨T, hT, _⟩ :=
    h.increments.strictlyStable.existsUnique_levyKhintchineTriple
  letI : SigmaFinite T.levyMeasure :=
    T.levyMeasure_isLevyMeasure.sigmaFinite
  exact h.measure_fullEntrance_pos_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε

/-- The source's left-open, right-closed endpoint event has positive
probability for `α < 1`, without exposing its Lévy--Khintchine triple. -/
theorem IsStableLevyProcess.measure_sourceEntrance_pos_indexLTOne
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorEvent X 0 1 (c - 1) (c + 1) ∩
      {ω | c - b - ε < segmentIncrement X 0 1 ω ⊤ ∧
        segmentIncrement X 0 1 ω ⊤ ≤ c - b + ε}) := by
  obtain ⟨T, hT, _⟩ :=
    h.increments.strictlyStable.existsUnique_levyKhintchineTriple
  letI : SigmaFinite T.levyMeasure :=
    T.levyMeasure_isLevyMeasure.sigmaFinite
  exact h.measure_sourceEntrance_pos_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε

/-- Relation (21)'s stable-scaled entrance probability has a limit equal to
the unit-time value, and that value is positive, with the Lévy--Khintchine
representation chosen internally from strict stability. -/
theorem IsStableLevyProcess.tendsto_measure_scaledEntrance_corridorReturn_indexLTOne
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
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
  obtain ⟨T, hT, _⟩ :=
    h.increments.strictlyStable.existsUnique_levyKhintchineTriple
  letI : SigmaFinite T.levyMeasure :=
    T.levyMeasure_isLevyMeasure.sigmaFinite
  exact h.tendsto_measure_scaledEntrance_corridorReturn_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε

/-- For `α < 1`, the shifted-corridor logarithmic comparison follows from
the source CDF assumption alone; the Lévy--Khintchine triple is chosen inside
the proof. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_indexLTOne
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : α < 1)
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
  obtain ⟨T, hT, _⟩ :=
    h.increments.strictlyStable.existsUnique_levyKhintchineTriple
  letI : SigmaFinite T.levyMeasure :=
    T.levyMeasure_isLevyMeasure.sigmaFinite
  exact h.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero_of_poissonModel
    hα T hT hcdf b c ε hb hc hε δ hδ

end ProbabilityTheory

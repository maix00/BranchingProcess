module

public import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Core
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntrance
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntranceIndexOne
public import Probability.Distributions.Stable.Sign

/-!
# Feedback entrance specializations

Stable-index-specific conclusions that obtain the entrance probability from finite feedback constructions.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- For stable index greater than one, finite feedback blocks give the
fixed entrance probability, while the strict tube upper bound gives the
shrinking-corridor logarithmic limit. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 1 < α)
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
  have hp := h.measure_fullEntrance_pos_of_cdfAtZero hα hcdf
    b c ε hb hc hε
  exact h.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    hpos hneg b c ε hb hε.le hp δ hδ

/-- At index one, nondegenerate strict stability supplies the two-sided
tails about every target slope, so the complete comparison needs no
additional distributional assumption. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_indexOne
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess 1 μ X P)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  have hpos := h.increments.strictlyStable.measure_Ioi_pos_indexOne 0
  have hneg := h.increments.strictlyStable.measure_Iio_pos_indexOne 0
  have hp := h.measure_fullEntrance_pos_indexOne b c ε hb hc hε
  exact h.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    hpos hneg b c ε hb hε.le hp δ hδ


end ProbabilityTheory

end

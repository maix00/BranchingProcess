module

public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.Brownian.Skorokhod
public import Probability.Process.Path.Oscillation

@[expose] public section

/-!
# Brownian specializations of continuous-path range bounds

The path-space finite-cover argument is generic. This file contains only the
Brownian input that identifies the start-at-zero event and applies that
generic argument to a pre-Brownian real process.
-/

open MeasureTheory

namespace ProbabilityTheory.Process.Path

/-- The continuous-path law of a pre-Brownian process is supported on paths
starting at zero. -/
theorem IsPreBrownianReal.ae_continuousunitIntervalPath_startsAtZero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ path ∂P.map (continuousunitIntervalPath B hcontinuous),
      path (0 : unitInterval) = 0 := by
  rw [ae_map_iff
    (measurable_continuousunitIntervalPath B hcontinuous hmeasurable).aemeasurable
    isClosed_startsAtZeroSet.measurableSet]
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  rw [continuousunitIntervalPath_apply]
  have htime : unitIntervalToNNReal (0 : unitInterval) = 0 := by
    apply Subtype.ext
    rfl
  rw [htime]
  exact hω

/-- Brownian bounded-range probability is controlled by the fixed finite
minimum-location cover. -/
theorem IsPreBrownianReal.measure_continuousunitIntervalPath_rangeOscillation_le_finiteCorridorCover
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    (P.map (continuousunitIntervalPath B hcontinuous))
        (rangeOscillationSet width) ≤
      ∑ j : Fin count,
        (P.map (continuousunitIntervalPath B hcontinuous))
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) := by
  exact measure_rangeOscillationSet_le_finiteCorridorCover
    (P.map (continuousunitIntervalPath B hcontinuous)) hwidth hcount
    (IsPreBrownianReal.ae_continuousunitIntervalPath_startsAtZero
      hB hcontinuous hmeasurable)

end ProbabilityTheory.Process.Path

end

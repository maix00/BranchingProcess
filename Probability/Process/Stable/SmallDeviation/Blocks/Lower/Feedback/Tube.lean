/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Feedback.Probability
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Feedback.Scaling
/-!
# Stable linear tubes from positive short-block probabilities

* `IsStableLevyProcess.linearTube_probability_pos` states that, for
  `α > 1`, two-sided increment mass implies
  `P(∀ t ∈ [0,1], |X_t - v t| < η) > 0` for every `v ∈ ℝ` and `η > 0`.

The short-block positivity and scale choice use stability. The finite
feedback construction and its pathwise tube implication live in the general
uniform-block path module.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- For stable index greater than one, two-sided one-step mass and the
short-block scale give positive probability to every complete-path tube
around a prescribed linear path. -/
theorem IsStableLevyProcess.linearTube_probability_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 1 < α)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0))
    (v η : ℝ) (hη : 0 < η) :
    0 < P {ω | ∀ t : unitInterval,
      |X (UnitInterval.toNNReal t) ω - v * (t : ℝ)| < η} := by
  obtain ⟨r, R, hr, hrR, hevent⟩ :=
    h.exists_feedbackShortBlockWindows hα hpos hneg
      (η / 8) (by positivity) v (η / 16) (by positivity)
  obtain ⟨n, hn⟩ := hevent.exists
  rcases hn with ⟨hplus, hminus, hratio, hscale⟩
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let a : ℝ := (t : ℝ) ^ (1 / α)
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    exact NNReal.coe_pos.mpr (by dsimp [t]; positivity)
  obtain ⟨hcorrectPlus, hcorrectMinus⟩ :=
    h.positive_feedbackCorrectionBlocks n (η / 8) v r R
      hplus hminus hratio
  have hscaleA : R * a < η / 16 := by
    simpa [a, t, stableBlock_nnrealScale_eq] using hscale
  have hratioA : |v / ((n : ℝ) + 1)| < r * a / 2 := by
    have heq : |v / ((n : ℝ) + 1)| / a =
        |v| * ((n : ℝ) + 1) ^ (1 / α - 1) := by
      rw [show a = ((n : ℝ) + 1) ^ (-(1 / α)) by
        exact stableBlock_nnrealScale_eq α n]
      rw [Real.rpow_neg_eq_inv_rpow]
      simpa only [one_div] using stableBlock_drift_div_scale_eq α v n
    have hratio' : |v / ((n : ℝ) + 1)| / a < r / 2 := by
      rw [heq]
      exact hratio
    have := (div_lt_iff₀ ha).mp hratio'
    nlinarith
  have hr' : 0 ≤ r * a / 2 := by positivity
  have hR' : 0 ≤ (R + r / 2) * a := by
    have hRpos : 0 < R := lt_trans hr hrR
    exact mul_nonneg (by linarith) ha.le
  have hwidth :
      2 * ((R + r / 2) * a + η / 8 +
        |v / ((n : ℝ) + 1)|) < η := by
    have hra : r * a < R * a := mul_lt_mul_of_pos_right hrR ha
    linarith
  have hcorrectMinus' :
      0 < P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-(η / 8)) (η / 8) ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) -
          v / ((n : ℝ) + 1) ∈
            Set.Ioo (-((R + r / 2) * a)) (-(r * a / 2))}) := by
    simpa only [neg_mul, a, t] using hcorrectMinus
  have hrelative : 0 < P {ω | ∀ t : unitInterval,
      |X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)| < η} :=
    h.increments.indepIncrements.linearTube_probability_pos_of_feedbackBlocks
      h.toIsLevyProcess.stationaryIncrements
      (fun s => h.increments.aemeasurable_eval s) h.ae_cadlag
      n v (η / 8) (r * a / 2) ((R + r / 2) * a) η
      hr' hR' hwidth hcorrectPlus hcorrectMinus'
  have heq :
      {ω | ∀ t : unitInterval,
        |X (UnitInterval.toNNReal t) ω - v * (t : ℝ)| < η} =ᵐ[P]
      {ω | ∀ t : unitInterval,
        |X (UnitInterval.toNNReal t) ω - X 0 ω - v * (t : ℝ)| < η} := by
    filter_upwards [h.increments.ae_start_eq_zero] with ω hzero
    have hzero' : X 0 ω = 0 := by simpa using hzero
    apply propext
    simp [hzero']
  rw [measure_congr heq]
  exact hrelative

end ProbabilityTheory

end

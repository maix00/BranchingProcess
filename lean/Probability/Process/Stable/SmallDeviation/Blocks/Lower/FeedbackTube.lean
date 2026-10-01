module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackProbability
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.FeedbackBound
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackScaling

/-!
# A complete-path tube from finite feedback blocks

The full-path conclusion uses the stable process's almost-sure zero start and
càdlàg regularity. The positive probability input is the adaptive finite
block event, not a path-space support assumption.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.linearTube_probability_pos_of_feedbackBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (n : ℕ) (v δ r R η : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hwidth : 2 * (R + δ + |v / ((n : ℝ) + 1)|) < η)
    (hplus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) -
        v / ((n : ℝ) + 1) ∈ Set.Ioo r R}))
    (hminus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) -
        v / ((n : ℝ) + 1) ∈ Set.Ioo (-R) (-r)})) :
    0 < P {ω | ∀ t : unitInterval,
      |X (unitIntervalToNNReal t) ω - v * (t : ℝ)| < η} := by
  let success : Set Ω :=
    rationalUniformPrefixPath X (n + 1) (n + 1) (Nat.succ_pos n) ⁻¹'
      rationalFeedbackPrefixSet (Nat.succ_pos n) (n + 1)
        (fun j => v * (j.val : ℝ) / ((n : ℝ) + 1))
        (feedbackCorrectionSet δ (v / ((n : ℝ) + 1)) r R)
        (feedbackCorrectionSet δ (v / ((n : ℝ) + 1)) (-R) (-r))
  have hsuccess : 0 < P success := by
    simpa [success, Nat.cast_add] using
      h.feedbackPrefix_probability_pos_of_fullBlocks n
        (fun j => v * (j.val : ℝ) / ((n : ℝ) + 1)) δ
        (v / ((n : ℝ) + 1)) r R hplus hminus
  have hcongr : success =ᵐ[P]
      {ω | ∀ t : unitInterval,
        |X (unitIntervalToNNReal t) ω - v * (t : ℝ)| < η} ∩ success := by
    filter_upwards [h.ae_cadlag, h.increments.ae_start_eq_zero]
      with ω hcadlag hzero
    apply propext
    constructor
    · intro hs
      refine ⟨?_, hs⟩
      have hbound := rationalFeedback_fullPath_bound X ω hcadlag
        (Nat.succ_pos n) v δ r R η hr hR
        (by simpa [Nat.cast_add] using hwidth)
        (by simpa [success, Nat.cast_add] using hs)
      intro t
      have hzero' : X 0 ω = 0 := hzero
      simpa [hzero'] using hbound t
    · exact And.right
  rw [measure_congr hcongr] at hsuccess
  exact hsuccess.trans_le (measure_mono Set.inter_subset_left)

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
      |X (unitIntervalToNNReal t) ω - v * (t : ℝ)| < η} := by
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
  exact h.linearTube_probability_pos_of_feedbackBlocks n v (η / 8)
    (r * a / 2) ((R + r / 2) * a) η hr' hR' hwidth
    hcorrectPlus hcorrectMinus'

end ProbabilityTheory

end

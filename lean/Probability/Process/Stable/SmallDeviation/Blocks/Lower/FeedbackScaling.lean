/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.ShortTime
public import Order.Bounds.Feedback
public import MeasureTheory.Measure.TwoSidedWindow
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Drift relative to the stable scale of short blocks

For stable index greater than one, a fixed linear drift over a block of
length `1/(n+1)` is negligible compared with the block's stable scale.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter
open MeasureTheory
open scoped Topology NNReal

theorem tendsto_drift_over_stableScale_zero
    (α : ℝ) (hα : 1 < α) (v : ℝ) :
    Tendsto (fun n : ℕ =>
      v * ((n : ℝ) + 1) ^ (1 / α - 1)) atTop (𝓝 0) := by
  have hαpos : 0 < α := by linarith
  have hexp : 0 < 1 - 1 / α := by
    have hdiv : 1 / α < 1 := (div_lt_one hαpos).2 hα
    linarith
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add] using
      ((tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1))
  have hpow : Tendsto (fun n : ℕ =>
      ((n : ℝ) + 1) ^ (-(1 - 1 / α))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hexp).comp hbase
  convert hpow.const_mul v using 1 <;> simp [sub_eq_add_neg]

/-- The stable spatial scale of a block of length `1/(n+1)` vanishes. -/
theorem tendsto_stableBlockScale_zero
    (α : ℝ) (hα : 0 < α) (R : ℝ) :
    Tendsto (fun n : ℕ =>
      R * ((n : ℝ) + 1) ^ (-(1 / α))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def, Nat.cast_add] using
      ((tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
          (tendsto_add_atTop_nat 1))
  have hscale := (tendsto_rpow_neg_atTop (div_pos one_pos hα)).comp hbase
  simpa using hscale.const_mul R

/-- The two strict numerical bounds needed for feedback can be achieved
simultaneously at sufficiently fine uniform partitions when `α > 1`. -/
theorem eventually_stableFeedbackScale_bounds
    (α : ℝ) (hα : 1 < α) (v r R η : ℝ)
    (hr : 0 < r) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      |v| * ((n : ℝ) + 1) ^ (1 / α - 1) < r ∧
      R * ((n : ℝ) + 1) ^ (-(1 / α)) < η := by
  have hfirst :=
    (tendsto_drift_over_stableScale_zero α hα |v|).eventually_lt_const hr
  have hsecond :=
    (tendsto_stableBlockScale_zero α (by linarith) R).eventually_lt_const hη
  exact hfirst.and hsecond

/-- The normalized target drift in a uniform block is precisely the ratio
controlled by the preceding real-power limit. -/
theorem stableBlock_drift_div_scale_eq
    (α v : ℝ) (n : ℕ) :
    |v / ((n : ℝ) + 1)| /
        ((1 / ((n : ℝ) + 1)) ^ (1 / α)) =
      |v| * ((n : ℝ) + 1) ^ (1 / α - 1) := by
  let N : ℝ := (n : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  have hpow : N ^ (1 / α) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  change |v / N| / ((1 / N) ^ (1 / α)) =
    |v| * N ^ (1 / α - 1)
  rw [abs_div, abs_of_pos hN, Real.rpow_sub_one hN.ne']
  rw [show (1 / N) ^ (1 / α) = (N ^ (1 / α))⁻¹ by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow,
      Real.rpow_neg hN.le]]
  field_simp

/-- The nonnegative-real time parameter used by the path event has the same
real stable scale as the analytic partition formula. -/
theorem stableBlock_nnrealScale_eq
    (α : ℝ) (n : ℕ) :
    (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) =
      ((n : ℝ) + 1) ^ (-(1 / α)) := by
  have hN : 0 < (n : ℝ) + 1 := by positivity
  have hcast :
      ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) =
        1 / ((n : ℝ) + 1) := by
    norm_num [NNReal.coe_div]
  rw [hcast, one_div, ← Real.rpow_neg_eq_inv_rpow,
    Real.rpow_neg hN.le]

/-- Positive probability of both normalized short-block windows transfers
to actual endpoint corrections about the prescribed linear drift. -/
theorem IsStableLevyProcess.positive_feedbackCorrectionBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (_h : IsStableLevyProcess α μ X P)
    (n : ℕ) (δ v r R : ℝ)
    (hplus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
        (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈
          Set.Ioo r R}))
    (hminus : 0 < P (fullSegmentCorridorEvent X 0
      (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
      {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
        (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈
          Set.Ioo (-R) (-r)}))
    (hscale : |v| * ((n : ℝ) + 1) ^ (1 / α - 1) < r / 2) :
    let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let a : ℝ := (t : ℝ) ^ (1 / α)
    0 < P (fullSegmentCorridorEvent X 0 t (-δ) δ ∩
      {ω | (X t ω - X 0 ω) - v / ((n : ℝ) + 1) ∈
        Set.Ioo (r * a / 2) ((R + r / 2) * a)}) ∧
    0 < P (fullSegmentCorridorEvent X 0 t (-δ) δ ∩
      {ω | (X t ω - X 0 ω) - v / ((n : ℝ) + 1) ∈
        Set.Ioo (-(R + r / 2) * a) (-(r * a / 2))}) := by
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let a : ℝ := (t : ℝ) ^ (1 / α)
  have ha : 0 < a := by
    apply Real.rpow_pos_of_pos
    exact NNReal.coe_pos.mpr (by dsimp [t]; positivity)
  have hratio : |v / ((n : ℝ) + 1)| / a < r / 2 := by
    rw [show a = ((n : ℝ) + 1) ^ (-(1 / α)) by
      exact stableBlock_nnrealScale_eq α n]
    rw [Real.rpow_neg_eq_inv_rpow]
    have heq : |v / ((n : ℝ) + 1)| /
        ((n : ℝ) + 1)⁻¹ ^ (1 / α) =
          |v| * ((n : ℝ) + 1) ^ (1 / α - 1) := by
      simpa only [one_div] using stableBlock_drift_div_scale_eq α v n
    rw [heq]
    exact hscale
  constructor
  · apply hplus.trans_le
    apply measure_mono
    rintro ω ⟨hcorridor, hend⟩
    refine ⟨hcorridor, ?_⟩
    exact Real.feedback_positive_scaledWindow a r R
      (X t ω - X 0 ω) (v / ((n : ℝ) + 1)) ha hend hratio
  · apply hminus.trans_le
    apply measure_mono
    rintro ω ⟨hcorridor, hend⟩
    refine ⟨hcorridor, ?_⟩
    exact Real.feedback_negative_scaledWindow a r R
      (X t ω - X 0 ω) (v / ((n : ℝ) + 1)) ha hend hratio

/-- For two fixed positive-mass normalized endpoint windows, one and the
same sufficiently fine partition satisfies both joint path-and-endpoint
positivity statements and both feedback scale bounds. -/
theorem IsStableLevyProcess.eventually_feedbackShortBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hα : 1 < α)
    (δ : ℝ) (hδ : 0 < δ)
    (Jplus Jminus : Set ℝ)
    (hmeasPlus : MeasurableSet Jplus) (hmeasMinus : MeasurableSet Jminus)
    (hposPlus : 0 < μ Jplus) (hposMinus : 0 < μ Jminus)
    (v r R η : ℝ) (hr : 0 < r) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      0 < P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
          (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈ Jplus}) ∧
      0 < P (fullSegmentCorridorEvent X 0
        (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
        {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
          (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈ Jminus}) ∧
      |v| * ((n : ℝ) + 1) ^ (1 / α - 1) < r ∧
      R * ((n : ℝ) + 1) ^ (-(1 / α)) < η := by
  filter_upwards
    [h.eventually_fullShortCorridor_scaledIncrement_pos δ hδ
      Jplus hmeasPlus hposPlus,
     h.eventually_fullShortCorridor_scaledIncrement_pos δ hδ
      Jminus hmeasMinus hposMinus,
     eventually_stableFeedbackScale_bounds α hα v r R η hr hη]
    with n hplus hminus hscale
  exact ⟨hplus, hminus, hscale.1, hscale.2⟩

/-- Two-sided increment mass supplies fixed bounded normalized endpoint
windows, and a common sufficiently fine block count satisfies their joint
path-and-endpoint positivity and the drift and width bounds. -/
theorem IsStableLevyProcess.exists_feedbackShortBlockWindows
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hα : 1 < α)
    (hpos : 0 < μ (Set.Ioi 0)) (hneg : 0 < μ (Set.Iio 0))
    (δ : ℝ) (hδ : 0 < δ) (v η : ℝ) (hη : 0 < η) :
    ∃ r R : ℝ, 0 < r ∧ r < R ∧
      ∀ᶠ n : ℕ in atTop,
        0 < P (fullSegmentCorridorEvent X 0
          (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
          {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
            (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈
              Set.Ioo r R}) ∧
        0 < P (fullSegmentCorridorEvent X 0
          (1 / ((n : ℝ≥0) + 1)) (-δ) δ ∩
          {ω | (X (1 / ((n : ℝ≥0) + 1)) ω - X 0 ω) /
            (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (1 / α)) ∈
              Set.Ioo (-R) (-r)}) ∧
        |v| * ((n : ℝ) + 1) ^ (1 / α - 1) < r / 2 ∧
        R * ((n : ℝ) + 1) ^ (-(1 / α)) < η := by
  obtain ⟨r, R, hr, hrR, hplus, hminus⟩ :
      ∃ r R : ℝ, 0 < r ∧ r < R ∧
        0 < μ (Set.Ioo r R) ∧ 0 < μ (Set.Ioo (-R) (-r)) := by
    simpa using μ.exists_twoSidedWindow_around_pos 0 hpos hneg
  refine ⟨r, R, hr, hrR, ?_⟩
  exact h.eventually_feedbackShortBlocks hα δ hδ
    (Set.Ioo r R) (Set.Ioo (-R) (-r))
    measurableSet_Ioo measurableSet_Ioo hplus hminus
    v (r / 2) R η (half_pos hr) hη

end ProbabilityTheory

end

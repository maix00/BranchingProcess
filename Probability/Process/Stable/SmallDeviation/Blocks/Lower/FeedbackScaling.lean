module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.ShortTime
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

end ProbabilityTheory

end

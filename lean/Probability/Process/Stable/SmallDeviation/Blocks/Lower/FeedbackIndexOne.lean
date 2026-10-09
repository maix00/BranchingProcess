/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackTube

/-!
# Feedback tubes at stable index one

At index one the normalized target drift of a block is the fixed number
`v`. The endpoint windows therefore straddle `v`, rather than zero. The
finite feedback probability and complete-path bound require no changes.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped NNReal Topology

/-- Two-sided one-step mass around the prescribed slope gives positive
probability to a complete unit-time tube around that slope at index one. -/
theorem IsStableLevyProcess.linearTube_probability_pos_indexOne
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess 1 μ X P)
    (v η : ℝ) (hη : 0 < η)
    (habove : 0 < μ (Set.Ioi v)) (hbelow : 0 < μ (Set.Iio v)) :
    0 < P {ω | ∀ t : unitInterval,
      |X (UnitInterval.toNNReal t) ω - v * (t : ℝ)| < η} := by
  obtain ⟨r, R, hr, hrR, hwinPlus, hwinMinus⟩ :=
    μ.exists_twoSidedWindow_around_pos v habove hbelow
  have hshortPlus := h.eventually_fullShortCorridor_scaledIncrement_pos
    (η / 8) (by positivity) (Set.Ioo (v + r) (v + R))
    measurableSet_Ioo hwinPlus
  have hshortMinus := h.eventually_fullShortCorridor_scaledIncrement_pos
    (η / 8) (by positivity) (Set.Ioo (v - R) (v - r))
    measurableSet_Ioo hwinMinus
  have hsmallR :=
    (tendsto_stableBlockScale_zero 1 (by norm_num) R).eventually_lt_const
      (by positivity : 0 < η / 16)
  have hsmallV :=
    (tendsto_stableBlockScale_zero 1 (by norm_num) |v|).eventually_lt_const
      (by positivity : 0 < η / 16)
  obtain ⟨n, ⟨hplus, hminus, hRsmall, hVsmall⟩⟩ :=
    (hshortPlus.and (hshortMinus.and (hsmallR.and hsmallV))).exists
  let t : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let a : ℝ := (t : ℝ) ^ (1 / (1 : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    apply Real.rpow_pos_of_pos
    exact NNReal.coe_pos.mpr (by dsimp [t]; positivity)
  have haeq : a = 1 / ((n : ℝ) + 1) := by
    simp [a, t, Real.rpow_one]
  have hRsmall' : R * a < η / 16 := by
    simpa [a, t, stableBlock_nnrealScale_eq] using hRsmall
  have hVsmall' : |v / ((n : ℝ) + 1)| < η / 16 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1),
      div_eq_mul_inv]
    simpa [Real.rpow_neg_one] using hVsmall
  have hd : v / ((n : ℝ) + 1) = v * a := by
    rw [haeq]
    ring
  have hplusCorrect :
      0 < P (fullSegmentCorridorEvent X 0 t (-(η / 8)) (η / 8) ∩
        {ω | (X t ω - X 0 ω) - v / ((n : ℝ) + 1) ∈
          Set.Ioo (r * a) (R * a)}) := by
    apply hplus.trans_le
    apply measure_mono
    rintro ω ⟨hcorridor, hend⟩
    refine ⟨hcorridor, ?_⟩
    have hpos := hend.1
    have hupper := hend.2
    change v + r < (X t ω - X 0 ω) / a at hpos
    change (X t ω - X 0 ω) / a < v + R at hupper
    have hlo := (lt_div_iff₀ ha).mp hpos
    have hhi := (div_lt_iff₀ ha).mp hupper
    rw [hd]
    constructor <;> nlinarith
  have hminusCorrect :
      0 < P (fullSegmentCorridorEvent X 0 t (-(η / 8)) (η / 8) ∩
        {ω | (X t ω - X 0 ω) - v / ((n : ℝ) + 1) ∈
          Set.Ioo (-(R * a)) (-(r * a))}) := by
    apply hminus.trans_le
    apply measure_mono
    rintro ω ⟨hcorridor, hend⟩
    refine ⟨hcorridor, ?_⟩
    have hpos := hend.1
    have hupper := hend.2
    change v - R < (X t ω - X 0 ω) / a at hpos
    change (X t ω - X 0 ω) / a < v - r at hupper
    have hlo := (lt_div_iff₀ ha).mp hpos
    have hhi := (div_lt_iff₀ ha).mp hupper
    rw [hd]
    constructor <;> nlinarith
  have hwidth :
      2 * (R * a + η / 8 + |v / ((n : ℝ) + 1)|) < η := by
    linarith
  exact h.linearTube_probability_pos_of_feedbackBlocks n v (η / 8)
    (r * a) (R * a) η (by positivity)
    (mul_nonneg (le_of_lt (lt_trans hr hrR)) ha.le)
    hwidth (by simpa [t] using hplusCorrect)
    (by simpa [t] using hminusCorrect)

end ProbabilityTheory

end

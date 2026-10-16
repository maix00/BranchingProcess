/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Normal.BlockTail
public import Probability.Process.RandomWalk.Path.Skorokhod.Range

/-!
# Compact range control in the normal domain of attraction

The normal-domain truncated-tail and variance profiles give a uniform
whole-horizon range bound for the normalized step paths. No finite-variance
assumption is used.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- Normal attraction gives eventual compact-range control for the normalized
step-path laws. We fix the truncation radius and send the excursion threshold
to infinity, using the Feller tail profile and the unit normalized truncated
variance profile. -/
theorem exists_eventually_compactRange_bound_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε := by
  let profileError : ℝ := ε / 2
  have hprofileError : 0 < profileError := by dsimp [profileError]; linarith
  let thresholdLower : ℝ := max 1 (8 * (1 + profileError) / ε)
  obtain ⟨m, hm⟩ := exists_nat_gt thresholdLower
  let thresholdMultiplier : ℝ := m
  have hthreshold : 0 < thresholdMultiplier := by
    dsimp [thresholdMultiplier]
    exact lt_trans (by norm_num : (0 : ℝ) < 1)
      (lt_of_le_of_lt (le_max_left _ _) hm)
  have hone : 1 ≤ thresholdMultiplier := by
    dsimp [thresholdMultiplier]
    exact le_trans (le_max_left _ _) hm.le
  have hthresholdLarge : 8 * (1 + profileError) / ε < thresholdMultiplier := by
    dsimp [thresholdMultiplier] at hm ⊢
    exact lt_of_le_of_lt (le_max_right _ _) hm
  have hthresholdSq : thresholdMultiplier ≤ thresholdMultiplier ^ 2 := by
    nlinarith [sq_nonneg (thresholdMultiplier - 1)]
  have hinv : (thresholdMultiplier ^ 2)⁻¹ ≤ thresholdMultiplier⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hthreshold) hthreshold).2 hthresholdSq
  have hquadratic : 4 * (1 + profileError) / thresholdMultiplier ^ 2 ≤
      4 * (1 + profileError) / thresholdMultiplier := by
    calc
      4 * (1 + profileError) / thresholdMultiplier ^ 2 =
          4 * (1 + profileError) * (thresholdMultiplier ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ 4 * (1 + profileError) * thresholdMultiplier⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * (1 + profileError) / thresholdMultiplier := by
        rw [div_eq_mul_inv]
  have hquadraticSmall :
      4 * (1 + profileError) / thresholdMultiplier < ε / 2 := by
    rw [div_lt_iff₀ hthreshold]
    have := hthresholdLarge
    rw [div_lt_iff₀ hε] at this
    nlinarith
  have htotal : profileError +
      4 * (1 + profileError) / thresholdMultiplier ^ 2 < ε := by
    dsimp [profileError]
    linarith [hquadratic, hquadraticSmall]
  let length : ℕ → ℕ := fun n => n
  have hlength : ∀ᶠ n : ℕ in atTop, 0 < length n := by
    exact eventually_gt_atTop 0
  have hratio : ∀ᶠ n : ℕ in atTop, (length n : ℝ) / n ≤ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [length, hn']
  have hblock := eventually_measure_blockPrefixExceedance_le_of_gaussian
    (radiusMultiplier := 1) (thresholdMultiplier := thresholdMultiplier)
    (δ := 1) (ε := profileError) (length := length)
    h hnormalization (by norm_num) hthreshold (by norm_num)
    hprofileError hlength hratio
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnormalization n hn
  have hbound : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance 0 n (thresholdMultiplier * normalization n)) ≤
          ENNReal.ofReal
            (profileError + 4 * (1 + profileError) / thresholdMultiplier ^ 2) := by
    filter_upwards [hblock] with n hn
    simpa [length, one_mul] using hn
  refine ⟨Set.Icc (-thresholdMultiplier) thresholdMultiplier, isCompact_Icc, ?_⟩
  filter_upwards [hbound, hscale] with n hboundN hscaleN
  have hrange := RandomWalk.measure_normalizedStepPathLaw_rangeIn_closedInterval_compl_le_of_blockPrefixExceedance
    ν normalization n hthreshold hscaleN
    (ENNReal.ofReal
      (profileError + 4 * (1 + profileError) / thresholdMultiplier ^ 2)) hboundN
  exact hrange.trans (ENNReal.ofReal_le_ofReal htotal.le)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end

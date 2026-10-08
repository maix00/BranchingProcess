/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Normal.TruncatedMoment
public import Probability.Process.RandomWalk.Path.Truncation.Normalized

/-!
# Truncated local block bounds in the normal domain of attraction

The Gaussian-domain tail and variance profiles feed the generic random-walk
hard-truncation estimate. The deterministic bias is kept as a separate input
until it is derived from the source centering assumptions.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- In the centered Gaussian domain of attraction, hard truncation at any
fixed multiple of the norming scale has negligible accumulated mean on the
norming scale. This derives the centering error from the first absolute tail
moment, without assuming a finite second moment. -/
theorem tendsto_nat_mul_abs_truncatedIncrementMean_div_scale_zero_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {radiusMultiplier : ℝ} (hradius : 0 < radiusMultiplier) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n) atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tailMoment : ℝ → ℝ := fun x =>
    ∫ y, {z : ℝ | x < |z|}.indicator (fun z => |z|) y ∂ν
  have hnorm : IsStableNorming 2 ν normalization :=
    h.isStableNorming_two_of_gaussian hnormalization
  have hvariance := h.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
    hnormalization radiusMultiplier hradius
  have hscaleTop : Tendsto normalization atTop atTop := hnorm.2.1
  have hcutoffTop : Tendsto (fun n : ℕ => radiusMultiplier * normalization n)
      atTop atTop := (tendsto_id.const_mul_atTop hradius).comp hscaleTop
  have habsolute : Integrable (fun x : ℝ => |x|) ν := by
    simpa [Real.norm_eq_abs] using h.integrable_id_of_gaussian.norm
  have htailMoment := tendsto_radius_mul_discardedAbsFirstMoment_div_truncatedSecondMoment_zero
    habsolute h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
    h.tendsto_secondTailRatio_of_gaussian
  have htailMomentSeq : Tendsto (fun n : ℕ =>
      (radiusMultiplier * normalization n) *
        tailMoment (radiusMultiplier * normalization n) /
          V (radiusMultiplier * normalization n) / radiusMultiplier)
      atTop (nhds 0) := by
    simpa [Function.comp_def, tailMoment, V, hradius.ne'] using
      (htailMoment.comp hcutoffTop).div_const radiusMultiplier
  have hprofile : Tendsto (fun n : ℕ =>
      ((n : ℝ) * V (radiusMultiplier * normalization n) /
        normalization n ^ 2) *
        ((radiusMultiplier * normalization n) *
          tailMoment (radiusMultiplier * normalization n) /
            V (radiusMultiplier * normalization n) / radiusMultiplier))
      atTop (nhds (1 * 0)) := hvariance.mul htailMomentSeq
  have hVpos : ∀ᶠ n : ℕ in atTop,
      0 < V (radiusMultiplier * normalization n) :=
    hcutoffTop.eventually h.eventually_pos_truncatedSecondMoment_of_gaussian
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have hprofileEq : (fun n : ℕ =>
      ((n : ℝ) * V (radiusMultiplier * normalization n) /
        normalization n ^ 2) *
        ((radiusMultiplier * normalization n) *
          tailMoment (radiusMultiplier * normalization n) /
            V (radiusMultiplier * normalization n) / radiusMultiplier)) =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) * tailMoment (radiusMultiplier * normalization n) /
        normalization n := by
    filter_upwards [hVpos, hscalePos] with n hV hb
    dsimp [V, tailMoment]
    field_simp [ne_of_gt hradius, ne_of_gt hb]
    calc
      (↑n * truncatedSecondMoment ν (radiusMultiplier * normalization n) *
          ∫ y, {z : ℝ | radiusMultiplier * normalization n < |z|}.indicator
            (fun z => |z|) y ∂ν) *
          (truncatedSecondMoment ν (radiusMultiplier * normalization n))⁻¹ =
        (↑n * ∫ y, {z : ℝ | radiusMultiplier * normalization n < |z|}.indicator
          (fun z => |z|) y ∂ν) *
          (truncatedSecondMoment ν (radiusMultiplier * normalization n) *
            (truncatedSecondMoment ν (radiusMultiplier * normalization n))⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ (ne_of_gt hV), mul_one]
  have htailMomentNorm : Tendsto (fun n : ℕ => (n : ℝ) *
      tailMoment (radiusMultiplier * normalization n) / normalization n)
      atTop (nhds 0) := by
    simpa using hprofile.congr' hprofileEq
  have hmeanBound : ∀ n : ℕ,
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| ≤
        tailMoment (radiusMultiplier * normalization n) := by
    intro n
    exact abs_truncatedIncrementMean_le_integral_tail ν
      h.integrable_id_of_gaussian h.integral_eq_zero_of_gaussian
      (radiusMultiplier * normalization n)
  have hmeanNonneg : ∀ n : ℕ,
      0 ≤ (n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n := by
    intro n
    by_cases hn : 0 < n
    · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
        (hnormalization n hn).le
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      simp [hn0]
  have hmeanLe : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤
        (n : ℝ) * tailMoment (radiusMultiplier * normalization n) /
          normalization n := by
    filter_upwards [hscalePos, eventually_gt_atTop (0 : ℕ)] with n hb hn
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmeanBound n) (Nat.cast_nonneg n)) hb.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    htailMomentNorm (Filter.Eventually.of_forall hmeanNonneg) hmeanLe

/-- The accumulated truncation bias is eventually small on any block whose
length is at most a fixed fraction of the full time horizon. -/
theorem eventually_truncatedIncrementBias_le_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {radiusMultiplier thresholdMultiplier δ : ℝ}
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) {length : ℕ → ℕ}
    (hlengthRatio : ∀ᶠ n : ℕ in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n : ℕ in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2 := by
  have hnormBias := tendsto_nat_mul_abs_truncatedIncrementMean_div_scale_zero_of_gaussian
    h hnormalization hradius
  let η : ℝ := thresholdMultiplier / (2 * (δ + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n < η :=
    hnormBias.eventually (Iio_mem_nhds hη)
  filter_upwards [hlengthRatio, hsmall, eventually_gt_atTop (0 : ℕ)]
    with n hratio hnsmall hn
  have hscale := hnormalization n hn
  have hratioNonneg : 0 ≤ (length n : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hbiasNonneg : 0 ≤ (n : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)) hscale.le
  have hratioBound : (length n : ℝ) / n ≤ δ + 1 := by linarith
  have hproduct : (length n : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
        normalization n =
      ((length n : ℝ) / n) *
        ((n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n) := by
    field_simp [ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn)]
  rw [hproduct]
  calc
    ((length n : ℝ) / n) *
        ((n : ℝ) *
          |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
            normalization n) ≤ (δ + 1) * η :=
      mul_le_mul hratioBound (le_of_lt hnsmall) hbiasNonneg (by positivity)
    _ = thresholdMultiplier / 2 := by dsimp [η]; field_simp

/-- A centered Gaussian-domain random walk has the generic one-block
excursion estimate once its hard-truncation bias is controlled. The profile
error `ε` can be chosen arbitrarily small; the result applies without a
finite-variance assumption. -/
theorem eventually_measure_blockPrefixExceedance_le_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {radiusMultiplier thresholdMultiplier δ ε : ℝ}
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (hε : 0 < ε) {length : ℕ → ℕ}
    (hlength : ∀ᶠ n : ℕ in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n : ℕ in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance 0 (length n)
          (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (ε + 4 * (1 + ε) / thresholdMultiplier ^ 2)) := by
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnormalization n hn
  have hbias := eventually_truncatedIncrementBias_le_of_gaussian h
    hnormalization hradius hthreshold hδ hlengthRatio
  exact eventually_measure_blockPrefixExceedance_le_of_normalizedTruncationProfiles
    ν hthreshold hδ hε hscale hlength hlengthRatio
    (h.tendsto_nat_mul_twoSidedTail_mul_of_gaussian hnormalization radiusMultiplier hradius)
    (h.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
      hnormalization radiusMultiplier hradius)
    hbias

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end

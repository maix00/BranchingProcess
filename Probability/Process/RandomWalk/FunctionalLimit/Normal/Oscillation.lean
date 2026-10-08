/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.BlockOscillation
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.BlockTail

/-!
# Oscillation bounds in the normal domain of attraction

The generic Skorokhod block criterion is combined here with the normal-domain
hard-truncation profiles. This module supplies distribution-specific local
probability bounds, while path compactness remains in the general functional
limit layer.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- A convenient coefficient for the Gaussian-domain one-block estimate at
threshold `ε / 2`, using profile error one. -/
noncomputable def gaussianOscillationBlockCoefficient (ε : ℝ) : ℝ :=
  1 + 4 * (1 + 1) / (ε / 2) ^ 2

theorem gaussianOscillationBlockCoefficient_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gaussianOscillationBlockCoefficient ε := by
  unfold gaussianOscillationBlockCoefficient
  positivity

/-- The Gaussian-domain one-block estimate controls failures of the
double-excursion criterion. This is the finite-window probability input to
the general oscillation-partition construction. -/
theorem eventually_measure_not_hasDoubleExcursionBound_le_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {radiusMultiplier ε endpointDelta blockFraction : ℝ}
    (hradius : 0 < radiusMultiplier) (hε : 0 < ε)
    (_hendpointDelta : 0 < endpointDelta) (hblockFraction : 0 ≤ blockFraction)
    (width : ℕ → ℕ) (hwidth : ∀ n, 0 < width n)
    (hwidthLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * endpointDelta ≤ width n)
    (hlengthRatio : ∀ᶠ n : ℕ in atTop,
      (2 * width n : ℝ) / n ≤ blockFraction) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasDoubleExcursionBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤
        ((n / width n + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal
            (blockFraction * gaussianOscillationBlockCoefficient ε)) ^ 2 := by
  let length : ℕ → ℕ := fun n => 2 * width n
  have hlength : ∀ n, 0 < length n := by
    intro n
    dsimp [length]
    exact Nat.mul_pos (by norm_num) (hwidth n)
  have hratio : ∀ᶠ n : ℕ in atTop, (length n : ℝ) / n ≤ blockFraction := by
    filter_upwards [hlengthRatio] with n hn
    simpa [length] using hn
  have hblock := eventually_measure_blockPrefixExceedance_le_of_gaussian
    (thresholdMultiplier := ε / 2) (δ := blockFraction) (ε := 1)
    (length := length) h hnormalization hradius (by positivity) hblockFraction
    (by norm_num : 0 < (1 : ℝ)) (Filter.Eventually.of_forall hlength) hratio
  have hblock' : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        (blockPrefixExceedance 0 (2 * width n)
          (ε * normalization n / 2)) ≤
        ENNReal.ofReal
          (blockFraction * gaussianOscillationBlockCoefficient ε) := by
    filter_upwards [hblock] with n hn
    have hthreshold : (ε / 2) * normalization n =
        ε * normalization n / 2 := by ring
    have hcoefficient : blockFraction *
        (1 + 4 * (1 + 1) / (ε / 2) ^ 2) =
          blockFraction * gaussianOscillationBlockCoefficient ε := by
      rfl
    simpa [length, hthreshold, hcoefficient] using hn
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnormalization n hn
  exact eventually_measure_not_hasDoubleExcursionBound_le_of_blockPrefixBound
    hε (ENNReal.ofReal
      (blockFraction * gaussianOscillationBlockCoefficient ε)) hscale width hwidth
    hwidthLower hblock'

/-- The Gaussian-domain one-block estimate also controls the two endpoint
windows in Billingsley's endpoint oscillation criterion. -/
theorem eventually_measure_not_hasEndpointOscillationBound_le_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n)
    {radiusMultiplier ε endpointDelta blockFraction : ℝ}
    (hradius : 0 < radiusMultiplier) (hε : 0 < ε)
    (hendpointDelta : 0 < endpointDelta) (hblockFraction : 0 ≤ blockFraction)
    (width : ℕ → ℕ)
    (hwidthLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * endpointDelta ≤ width n)
    (hlengthRatio : ∀ᶠ n : ℕ in atTop,
      (width n : ℝ) / n ≤ blockFraction) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasEndpointOscillationBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤
        2 * ENNReal.ofReal
          (blockFraction * gaussianOscillationBlockCoefficient ε) := by
  have hlength : ∀ᶠ n : ℕ in atTop, 0 < width n := by
    filter_upwards [hwidthLower, eventually_gt_atTop (0 : ℕ)] with n hlow hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hwR : 0 < (width n : ℝ) :=
      lt_of_lt_of_le (mul_pos hnR hendpointDelta) hlow
    exact_mod_cast hwR
  have hblock := eventually_measure_blockPrefixExceedance_le_of_gaussian
    (thresholdMultiplier := ε / 2) (δ := blockFraction) (ε := 1)
    (length := width) h hnormalization hradius (by positivity) hblockFraction
    (by norm_num : 0 < (1 : ℝ)) hlength hlengthRatio
  have hblock' : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        (blockPrefixExceedance 0 (width n)
          (ε * normalization n / 2)) ≤
        ENNReal.ofReal
          (blockFraction * gaussianOscillationBlockCoefficient ε) := by
    filter_upwards [hblock] with n hn
    have hthreshold : (ε / 2) * normalization n =
        ε * normalization n / 2 := by ring
    have hcoefficient : blockFraction *
        (1 + 4 * (1 + 1) / (ε / 2) ^ 2) =
          blockFraction * gaussianOscillationBlockCoefficient ε := by
      rfl
    simpa [hthreshold, hcoefficient] using hn
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnormalization n hn
  exact eventually_measure_not_hasEndpointOscillationBound_le_of_blockPrefixBound
    hε (ENNReal.ofReal
      (blockFraction * gaussianOscillationBlockCoefficient ε)) hscale width
    hwidthLower hblock'

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end

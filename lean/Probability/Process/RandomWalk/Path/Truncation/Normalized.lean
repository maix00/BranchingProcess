/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Probability.Process.RandomWalk.Path.Truncation.Maximal.SecondMoment

/-!
# Normalized local block bounds under hard truncation

This module converts the finite-cutoff maximal inequality into a bound at a
chosen spatial scale. The tail, truncated-second-moment, and truncation-bias
inputs stay explicit, so stable-domain applications can supply their own
asymptotics without assuming a global second moment.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A normalized one-block excursion bound. If the block length is at most a
`δ` fraction of the sample size, the normalized discarded-tail cost is at
most `δ * tailBound`; the centered truncated part costs at most
`4 * δ * momentBound / thresholdMultiplier^2`. The only centering input is
the displayed truncation-bias margin. -/
theorem measure_blockPrefixExceedance_le_of_normalizedTruncationBounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (sampleSize length : ℕ)
    {scale radiusMultiplier thresholdMultiplier δ tailBound momentBound : ℝ}
    (hsample : 0 < sampleSize) (hscale : 0 < scale) (hlength : 0 < length)
    (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (htailBound : 0 ≤ tailBound) (hmomentBound : 0 ≤ momentBound)
    (hlengthRatio : (length : ℝ) / sampleSize ≤ δ)
    (htail : (sampleSize : ℝ) *
      ν.real {x : ℝ | radiusMultiplier * scale < |x|} ≤ tailBound)
    (hmoment : (sampleSize : ℝ) *
      truncatedSecondMoment ν (radiusMultiplier * scale) / scale ^ 2 ≤ momentBound)
    (hbias : (length : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * scale)| / scale ≤
        thresholdMultiplier / 2) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance 0 length (thresholdMultiplier * scale)) ≤
      ENNReal.ofReal
        (δ * (tailBound + 4 * momentBound / thresholdMultiplier ^ 2)) := by
  let radius : ℝ := radiusMultiplier * scale
  let mean : ℝ := truncatedIncrementMean ν radius
  let gap : ℝ := thresholdMultiplier * scale -
    (length : ℝ) * |mean|
  let normalizedGap : ℝ := gap / scale
  have hsample' : (0 : ℝ) < sampleSize := by exact_mod_cast hsample
  have hlengthBound : (length : ℝ) ≤ δ * sampleSize :=
    (div_le_iff₀ hsample').mp hlengthRatio
  have hbias' : (length : ℝ) * |mean| ≤ thresholdMultiplier / 2 * scale := by
    dsimp [mean, radius]
    exact (div_le_iff₀ hscale).mp hbias
  have hgapPos : 0 < gap := by
    dsimp [gap]
    nlinarith [mul_pos hthreshold hscale]
  have hnormalizedGap : thresholdMultiplier / 2 ≤ normalizedGap := by
    dsimp [normalizedGap, gap]
    rw [le_div_iff₀ hscale]
    nlinarith
  have hgapInput : (length : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * scale)| <
        thresholdMultiplier * scale := by
    dsimp [mean, radius] at hbias' ⊢
    nlinarith [mul_pos hthreshold hscale]
  have hmomentNonneg : 0 ≤ truncatedSecondMoment ν radius := by
    rw [truncatedSecondMoment]
    exact setIntegral_nonneg measurableSet_Icc fun x _ => sq_nonneg x
  have hnormalizedMomentNonneg : 0 ≤
      (sampleSize : ℝ) * truncatedSecondMoment ν radius / scale ^ 2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hmomentNonneg) (sq_nonneg _)
  have hratioMoment :
      (length : ℝ) / sampleSize *
          ((sampleSize : ℝ) * truncatedSecondMoment ν radius / scale ^ 2) ≤
        δ * momentBound := by
    exact mul_le_mul hlengthRatio hmoment hnormalizedMomentNonneg hδ
  have hnormalizedVariance :
      (length : ℝ) * truncatedSecondMoment ν radius / gap ^ 2 ≤
        δ * momentBound * 4 / thresholdMultiplier ^ 2 := by
    have hden : (thresholdMultiplier / 2) ^ 2 ≤ normalizedGap ^ 2 :=
      (sq_le_sq₀ (le_of_lt (by positivity : 0 < thresholdMultiplier / 2))
        (le_of_lt (lt_of_lt_of_le (by positivity) hnormalizedGap))).2
        hnormalizedGap
    have hdenPos : 0 < (thresholdMultiplier / 2) ^ 2 :=
      sq_pos_of_pos (by positivity)
    have hgapSqPos : 0 < normalizedGap ^ 2 :=
      sq_pos_of_pos (lt_of_lt_of_le (by positivity) hnormalizedGap)
    have hinv := (inv_le_inv₀ hgapSqPos hdenPos).2 hden
    have hratioForm :
        (length : ℝ) * truncatedSecondMoment ν radius / gap ^ 2 =
          ((length : ℝ) / sampleSize *
            ((sampleSize : ℝ) * truncatedSecondMoment ν radius / scale ^ 2)) /
            normalizedGap ^ 2 := by
      dsimp [normalizedGap, gap]
      field_simp [ne_of_gt hsample', ne_of_gt hscale, ne_of_gt hgapPos]
    rw [hratioForm]
    calc
      _ ≤ (δ * momentBound) / normalizedGap ^ 2 :=
        div_le_div_of_nonneg_right hratioMoment (le_of_lt hgapSqPos)
      _ = δ * momentBound * (normalizedGap ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ δ * momentBound * ((thresholdMultiplier / 2) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hδ hmomentBound)
      _ = δ * momentBound * 4 / thresholdMultiplier ^ 2 := by
        field_simp
        norm_num
  have htailReal : (length : ℝ) *
      ν.real {x : ℝ | radiusMultiplier * scale < |x|} ≤ δ * tailBound := by
    calc
      _ ≤ δ * ((sampleSize : ℝ) *
          ν.real {x : ℝ | radiusMultiplier * scale < |x|}) :=
        (mul_le_mul_of_nonneg_right hlengthBound measureReal_nonneg).trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hδ
  have htailENN : (length : ENNReal) *
      ν {x : ℝ | radiusMultiplier * scale < |x|} ≤
        ENNReal.ofReal (δ * tailBound) := by
    have hEq : (length : ENNReal) *
        ν {x : ℝ | radiusMultiplier * scale < |x|} =
          ENNReal.ofReal ((length : ℝ) *
            ν.real {x : ℝ | radiusMultiplier * scale < |x|}) := by
      calc
        _ = ENNReal.ofReal (length : ℝ) *
            ENNReal.ofReal (ν.real {x : ℝ | radiusMultiplier * scale < |x|}) := by
              rw [ENNReal.ofReal_natCast, ofReal_measureReal]
        _ = _ := by rw [← ENNReal.ofReal_mul (Nat.cast_nonneg length)]
    rw [hEq]
    exact ENNReal.ofReal_le_ofReal htailReal
  have hlengthSub : length - 1 + 1 = length := by omega
  have hbase := measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded
    ν 1 (length - 1) (by simpa [hlengthSub] using hgapInput)
  have hbaseBound :
      (iidSequenceLaw ν) {path : ℕ → ℝ |
        ∃ j < 1, ∃ k ∈ Finset.range length,
          thresholdMultiplier * scale ≤
            |AdditivePath.blockSum (j * (length - 1)) (k + 1) path|} ≤
        (length : ENNReal) * ν {x : ℝ | radiusMultiplier * scale < |x|} +
          ENNReal.ofReal
            ((length : ℝ) * truncatedSecondMoment ν radius / gap ^ 2) := by
    simpa [hlengthSub, radius, gap, Nat.one_mul,
      truncatedCenteredSecondBound] using hbase
  have hsubset : blockPrefixExceedance 0 length
        (thresholdMultiplier * scale) ⊆
      {path : ℕ → ℝ | ∃ j < 1, ∃ k ∈ Finset.range length,
        thresholdMultiplier * scale ≤
          |AdditivePath.blockSum (j * (length - 1)) (k + 1) path|} := by
    intro path hpath
    obtain ⟨k, hk⟩ := hpath
    refine ⟨0, by omega, k.val, Finset.mem_range.mpr k.isLt, ?_⟩
    simpa [Nat.zero_mul] using hk
  have hbase' :
      (iidSequenceLaw ν) (blockPrefixExceedance 0 length
        (thresholdMultiplier * scale)) ≤
        (length : ENNReal) * ν {x : ℝ | radiusMultiplier * scale < |x|} +
          ENNReal.ofReal
            ((length : ℝ) * truncatedSecondMoment ν radius / gap ^ 2) :=
    (measure_mono hsubset).trans hbaseBound
  calc
    (iidSequenceLaw ν) (blockPrefixExceedance 0 length
        (thresholdMultiplier * scale)) ≤
        (length : ENNReal) * ν {x : ℝ | radiusMultiplier * scale < |x|} +
          ENNReal.ofReal
            ((length : ℝ) * truncatedSecondMoment ν radius / gap ^ 2) := hbase'
    _ ≤ ENNReal.ofReal (δ * tailBound) +
          ENNReal.ofReal (δ * momentBound * 4 / thresholdMultiplier ^ 2) :=
        add_le_add htailENN (ENNReal.ofReal_le_ofReal hnormalizedVariance)
    _ = ENNReal.ofReal
        (δ * (tailBound + 4 * momentBound / thresholdMultiplier ^ 2)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hδ htailBound)
        (by positivity : 0 ≤ δ * momentBound * 4 / thresholdMultiplier ^ 2)]
      congr 1
      ring

end ProbabilityTheory.RandomWalk

end

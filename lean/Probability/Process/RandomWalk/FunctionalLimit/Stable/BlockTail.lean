/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Tail
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Centering
public import Probability.Process.RandomWalk.Path.Truncation.Normalized

/-!
# Local block tails under a stable norming

The regular-variation limits for the discarded tail and truncated second
moment turn the normalized hard-truncation estimate into an eventual
small-block bound. The truncation-bias margin is an explicit hypothesis and
is not inferred from stable attraction here.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Under a stable norming with regularly varying two-sided tail, a block
whose length is at most a `δ` fraction of the sample size has an eventual
excursion bound of order `δ`. The centering condition is stated explicitly
at the truncation scale; a source-specific adapter must prove it from the
random-walk centering convention. -/
theorem eventually_measure_blockPrefixExceedance_le_of_stableNorming
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ)
    (hbias : ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedance 0 (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) := by
  let tailBound : ℝ := ((2 - α) / α) * radiusMultiplier ^ (-α) + 1
  let momentBound : ℝ := radiusMultiplier ^ (2 - α) + 1
  have htailBoundPos : 0 < tailBound := by
    dsimp [tailBound]
    positivity
  have hmomentBoundPos : 0 < momentBound := by
    dsimp [momentBound]
    positivity
  have htailLimit := hnorm.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
    hα₀ hα₂ htail hradius
  have htailBoundEventual : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * ν.real
        {x : ℝ | radiusMultiplier * normalization n < |x|} ≤ tailBound := by
    have hmargin :
        (((2 - α) / α) * radiusMultiplier ^ (-α)) < tailBound := by
      dsimp [tailBound]
      linarith
    filter_upwards [htailLimit.eventually
      (Iio_mem_nhds hmargin)] with n hn
    exact le_of_lt (by simpa using hn)
  have hmomentLimit :=
    hnorm.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq
      hα₀ hα₂ htail hradius
  have hmomentBoundEventual : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * truncatedSecondMoment ν
          (radiusMultiplier * normalization n) / normalization n ^ 2 ≤ momentBound := by
    have hmargin : radiusMultiplier ^ (2 - α) < momentBound := by
      dsimp [momentBound]
      linarith
    filter_upwards [hmomentLimit.eventually
      (Iio_mem_nhds hmargin)] with n hn
    exact le_of_lt (by simpa using hn)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hlength, hlengthRatio, hbias, htailBoundEventual,
      hmomentBoundEventual, hscalePos, eventually_gt_atTop (0 : ℕ)]
    with n hlengthn hratioN hbiasN htailN hmomentN hscaleN hn
  exact measure_blockPrefixExceedance_le_of_normalizedTruncationBounds
    ν n (length n) hn hscaleN hlengthn hthreshold hδ
    (le_of_lt htailBoundPos) (le_of_lt hmomentBoundPos)
    hratioN htailN hmomentN hbiasN

/-- For `0 < α < 1`, the uncentered stable-domain convention supplies the
truncation-bias margin automatically once the block fraction is sufficiently
small. The resulting local block estimate has no extra centering premise. -/
theorem eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_lt_one
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (δpos : 0 < δ)
    (hsmall : δ * truncationBiasConstant α radiusMultiplier <
      thresholdMultiplier / 2)
    (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedance 0 (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) := by
  have hbias := eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one
    hnorm hα₀ hα₁ htail hradius δpos hsmall hlengthRatio
  exact eventually_measure_blockPrefixExceedance_le_of_stableNorming
    hnorm hα₀ (by linarith [hα₁] : α < 2) htail hradius hthreshold
    δpos.le length hlength hlengthRatio hbias

/-- For `1 < α < 2`, a centered law with finite first absolute moment
supplies the truncation-bias margin from the discarded-tail Karamata
asymptotic. The local block estimate then follows without a separate bias
premise. -/
theorem eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_gt_one
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (δpos : 0 < δ)
    (hsmall : δ * discardedTailBiasConstant α radiusMultiplier <
      thresholdMultiplier / 2)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedance 0 (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) := by
  have hbias := eventually_truncatedIncrementBias_le_of_stableNorming_of_index_gt_one
    hnorm hα₀ hα₁ hα₂ htail hradius hint hcentered δpos hsmall hlengthRatio
  exact eventually_measure_blockPrefixExceedance_le_of_stableNorming
    hnorm hα₀ hα₂ htail hradius hthreshold δpos.le length hlength hlengthRatio hbias

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

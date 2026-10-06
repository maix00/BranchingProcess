/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.BlockTail

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

example {α radiusMultiplier : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (∫ x, min |x| (radiusMultiplier * normalization n) ∂ν) /
        normalization n) atTop (nhds (truncationBiasConstant α radiusMultiplier)) :=
  ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.tendsto_nat_mul_cappedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
    hnorm hα₀ hα₁ htail hradius

example {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 < δ)
    (hsmall : δ * truncationBiasConstant α radiusMultiplier <
      thresholdMultiplier / 2)
    (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedance 0 (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) :=
  eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_lt_one
    hnorm hα₀ hα₁ htail hradius hthreshold hδ hsmall length hlength hlengthRatio

example {radius scale : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hradius : 0 < radius) (hscale : 0 < scale) :
    |truncatedIncrementMean ν (radius * scale)| / scale ≤
      |∫ x, Real.sin (x / scale) ∂ν| +
        (radius / 6) * truncatedSecondMoment ν (radius * scale) / scale ^ 2 +
        ν.real {x : ℝ | radius * scale < |x|} :=
  abs_truncatedIncrementMean_div_le_sineIntegral_add_truncatedMoment_tail
    ν hradius hscale

example {radiusMultiplier : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hradius : 0 < radiusMultiplier)
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * |truncatedIncrementMean ν
        (radiusMultiplier * normalization n)| / normalization n ≤
          indexOneTruncationBiasConstant radiusMultiplier :=
  ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.eventually_nat_mul_abs_truncatedIncrementMean_div_le_of_index_one
    hnorm htail hradius hcenter

example {radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hcenter : IsMogulskiiIndexOneCentered ν normalization)
    (hδ : 0 < δ)
    (hsmall : δ * indexOneTruncationBiasConstant radiusMultiplier <
      thresholdMultiplier / 2)
    (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
          (blockPrefixExceedance 0 (length n)
            (thresholdMultiplier * normalization n)) ≤
        ENNReal.ofReal
          (δ * (radiusMultiplier⁻¹ + 1 +
            4 * (radiusMultiplier + 1) / thresholdMultiplier ^ 2)) :=
  eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_one
    hnorm htail hradius hthreshold hcenter hδ hsmall length hlength hlengthRatio

#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.tendsto_nat_mul_cappedAbsFirstMoment_div_normalization_of_regularlyVaryingTail
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_truncatedIncrementBias_le_of_stableNorming_of_index_lt_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_lt_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.abs_truncatedIncrementMean_div_le_sineIntegral_add_truncatedMoment_tail
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.IsStableNorming.eventually_nat_mul_abs_truncatedIncrementMean_div_le_of_index_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_truncatedIncrementBias_le_of_stableNorming_of_index_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming_of_index_one

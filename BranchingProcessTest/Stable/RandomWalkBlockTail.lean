/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.BlockTail

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

example {α radiusMultiplier thresholdMultiplier δ : ℝ}
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
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2)) :=
  eventually_measure_blockPrefixExceedance_le_of_stableNorming hnorm hα₀ hα₂
    htail hradius hthreshold hδ length hlength hlengthRatio hbias

example {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (start leftLength rightLength : ℕ → ℕ)
    (hleftLength : ∀ᶠ n in atTop, 0 < leftLength n)
    (hrightLength : ∀ᶠ n in atTop, 0 < rightLength n)
    (hleftRatio : ∀ᶠ n in atTop, (leftLength n : ℝ) / n ≤ δ)
    (hrightRatio : ∀ᶠ n in atTop, (rightLength n : ℝ) / n ≤ δ)
    (hleftBias : ∀ᶠ n in atTop,
      (leftLength n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2)
    (hrightBias : ∀ᶠ n in atTop,
      (rightLength n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n) (leftLength n)
            (thresholdMultiplier * normalization n) ∩
          blockPrefixExceedance (start n + leftLength n) (rightLength n)
            (thresholdMultiplier * normalization n)) ≤
        (ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2))) ^ 2 :=
  eventually_measure_adjacentVariableBlockPrefixExceedance_le_of_stableNorming
    hnorm hα₀ hα₂ htail hradius hthreshold hδ start leftLength rightLength
    hleftLength hrightLength hleftRatio hrightRatio hleftBias hrightBias

#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_adjacentBlockPrefixExceedance_le_of_stableNorming
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_adjacentVariableBlockPrefixExceedance_le_of_stableNorming
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_stableNorming

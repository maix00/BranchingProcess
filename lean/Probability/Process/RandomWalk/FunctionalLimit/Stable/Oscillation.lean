/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.BlockTail
public import Probability.Process.RandomWalk.Path.Block.Law.FirstCrossing
public import Probability.Process.RandomWalk.Path.Skorokhod.Oscillation

/-!
# Stable-domain bounds for two ordered block excursions

The generic random-walk layer proves that two ordered large oscillations in
one finite window require a first crossing followed by a fresh excursion.
This file supplies the stable-domain one-block estimate and obtains the
corresponding squared local bound. It is a local oscillation estimate; the
global Skorokhod tightness criterion still requires a covering argument and
endpoint control.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- In the stable domain, two ordered excursions in a block occupying at most
a `δ` fraction of the time horizon have probability `O(δ²)`. The two
excursions are separated at the first crossing of the local threshold, so
the estimate uses independent increments after a discrete stopping time.

The excursion threshold in the event is twice `thresholdMultiplier` times
the stable norming. This factor is the triangle-inequality margin needed to
locate a first crossing before the second excursion. -/
theorem eventually_measure_twoOrderedBlockExcursions_le_of_stableNorming
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (start length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ)
    (hbias : ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
        (RandomWalk.twoOrderedBlockExcursions (start n) (length n)
          (2 * (thresholdMultiplier * normalization n))) ≤
        (ENNReal.ofReal
          (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2))) ^ 2 := by
  let oneBlockBound : ENNReal := ENNReal.ofReal
    (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
      4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2))
  have hblock := eventually_measure_blockPrefixExceedance_le_of_stableNorming_unitMargins
    hnorm hα₀ hα₂ htail hradius hthreshold hδ length hlength hlengthRatio hbias
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hblock, hscale] with n hblockN hscaleN
  have hblockN' : iidSequenceLaw ν
      (blockPrefixExceedance 0 (length n)
        (thresholdMultiplier * normalization n)) ≤ oneBlockBound := by
    simpa [oneBlockBound] using hblockN
  have hthresholdN : 0 < thresholdMultiplier * normalization n :=
    mul_pos hthreshold hscaleN
  calc
    _ = (iidSequenceLaw ν)
        (RandomWalk.twoOrderedPrefixExcursions (length n)
          (2 * (thresholdMultiplier * normalization n))) :=
      RandomWalk.measure_twoOrderedBlockExcursions_translate_eq ν
        (start n) (length n) _
    _ ≤ oneBlockBound ^ 2 :=
      RandomWalk.measure_twoOrderedPrefixExcursions_le_sq_of_blockBound
        ν (length n) hthresholdN oneBlockBound hblockN'

/-- Stable-domain probability bound for the union of local two-excursion
events over a finite deterministic grid. The number and placement of windows
may depend on the sample horizon; only their common length fraction and
centering estimate enter the bound. -/
theorem eventually_measure_iUnion_twoOrderedBlockExcursions_le_of_stableNorming
    {α radiusMultiplier thresholdMultiplier δ : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (count : ℕ → ℕ)
    (start : ∀ n, Fin (count n) → ℕ) (length : ℕ → ℕ)
    (hlength : ∀ᶠ n in atTop, 0 < length n)
    (hlengthRatio : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ δ)
    (hbias : ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ thresholdMultiplier / 2) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
        (⋃ j : Fin (count n),
          RandomWalk.twoOrderedBlockExcursions (start n j) (length n)
            (2 * (thresholdMultiplier * normalization n))) ≤
        (count n : ENNReal) *
          (ENNReal.ofReal
            (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
              4 * (radiusMultiplier ^ (2 - α) + 1) /
                thresholdMultiplier ^ 2))) ^ 2 := by
  let oneBlockBound : ENNReal := ENNReal.ofReal
    (δ * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
      4 * (radiusMultiplier ^ (2 - α) + 1) / thresholdMultiplier ^ 2))
  have hblock := eventually_measure_blockPrefixExceedance_le_of_stableNorming_unitMargins
    hnorm hα₀ hα₂ htail hradius hthreshold hδ length hlength hlengthRatio hbias
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hblock, hscale] with n hblockN hscaleN
  have hblockN' : iidSequenceLaw ν
      (blockPrefixExceedance 0 (length n)
        (thresholdMultiplier * normalization n)) ≤ oneBlockBound := by
    simpa [oneBlockBound] using hblockN
  have hthresholdN : 0 < thresholdMultiplier * normalization n :=
    mul_pos hthreshold hscaleN
  have hwindowBound (j : Fin (count n)) :
      iidSequenceLaw ν
        (RandomWalk.twoOrderedBlockExcursions (start n j) (length n)
          (2 * (thresholdMultiplier * normalization n))) ≤ oneBlockBound ^ 2 := by
    calc
      _ = iidSequenceLaw ν
          (RandomWalk.twoOrderedPrefixExcursions (length n)
            (2 * (thresholdMultiplier * normalization n))) :=
        RandomWalk.measure_twoOrderedBlockExcursions_translate_eq ν
          (start n j) (length n) _
      _ ≤ oneBlockBound ^ 2 :=
        RandomWalk.measure_twoOrderedPrefixExcursions_le_sq_of_blockBound
          ν (length n) hthresholdN oneBlockBound hblockN'
  have hunion : iidSequenceLaw ν
      (⋃ j : Fin (count n),
        RandomWalk.twoOrderedBlockExcursions (start n j) (length n)
          (2 * (thresholdMultiplier * normalization n))) ≤
        (count n : ENNReal) * oneBlockBound ^ 2 := by
    calc
      _ ≤ ∑' j : Fin (count n),
          iidSequenceLaw ν
            (RandomWalk.twoOrderedBlockExcursions (start n j) (length n)
              (2 * (thresholdMultiplier * normalization n))) := measure_iUnion_le _
      _ = ∑ j : Fin (count n),
          iidSequenceLaw ν
            (RandomWalk.twoOrderedBlockExcursions (start n j) (length n)
              (2 * (thresholdMultiplier * normalization n))) := by
        simp only [tsum_fintype]
      _ ≤ ∑ j : Fin (count n), oneBlockBound ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hwindowBound j
      _ = (count n : ENNReal) * oneBlockBound ^ 2 := by simp
  simpa [oneBlockBound] using hunion

/-- The stable local two-excursion estimate controls the probability that a
normalized random-walk path violates the generic Billingsley double-excursion
condition. The deterministic path-to-window implication is supplied by the
random-walk Skorokhod layer; this result only bounds the resulting finite
union. It does not alone produce a sequence of oscillation partitions. -/
theorem eventually_measure_not_hasDoubleExcursionBound_le_of_stableNorming
    {α radiusMultiplier ε endpointDelta blockFraction : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hε : 0 < ε)
    (hblockFraction : 0 ≤ blockFraction)
    (width : ℕ → ℕ) (hwidth : ∀ n, 0 < width n)
    (hwidthLower : ∀ᶠ n : ℕ in atTop, (n : ℝ) * endpointDelta ≤ width n)
    (hlengthRatio : ∀ᶠ n : ℕ in atTop,
      (2 * width n : ℝ) / n ≤ blockFraction)
    (hbias : ∀ᶠ n : ℕ in atTop,
      (2 * width n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ ε / 4) :
    ∀ᶠ n in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasDoubleExcursionBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤
        ((n / width n + 1 : ℕ) : ENNReal) *
          (ENNReal.ofReal
            (blockFraction * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
              4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2))) ^ 2 := by
  let count : ℕ → ℕ := fun n => n / width n + 1
  let starts : ∀ n, Fin (count n) → ℕ := fun n j => j.val * width n
  let length : ℕ → ℕ := fun n => 2 * width n
  have hlength : ∀ n, 0 < length n := by
    intro n
    dsimp [length]
    exact Nat.mul_pos (by norm_num) (hwidth n)
  have hlengthRatio' : ∀ᶠ n in atTop, (length n : ℝ) / n ≤ blockFraction := by
    filter_upwards [hlengthRatio] with n hn
    simpa [length] using hn
  have hbias' : ∀ᶠ n in atTop,
      (length n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ (ε / 2) / 2 := by
    filter_upwards [hbias] with n hn
    calc
      _ ≤ ε / 4 := by simpa [length] using hn
      _ = (ε / 2) / 2 := by ring
  have hlocal := eventually_measure_iUnion_twoOrderedBlockExcursions_le_of_stableNorming
    (thresholdMultiplier := ε / 2)
    hnorm hα₀ hα₂ htail hradius (by positivity) hblockFraction count starts length
    (Filter.Eventually.of_forall hlength) hlengthRatio' hbias'
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hlocal, hscale, hwidthLower, eventually_gt_atTop (0 : ℕ)]
      with n hlocalN hscaleN hwidthLowerN hn
  have hbadSubset :
      {increment | ¬ Skorokhod.HasDoubleExcursionBound
        (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
        endpointDelta ε} ⊆
      ⋃ j : Fin (count n),
        RandomWalk.twoOrderedBlockExcursions (starts n j) (length n)
          (ε * normalization n) := by
    intro increment hbad
    have hbridge := RandomWalk.normalizedStepCadlagPathIcc_not_hasDoubleExcursionBound_subset_windowGrid
      normalization n (by omega) hscaleN endpointDelta ε (width n) (hwidth n)
      hwidthLowerN increment hbad
    simpa [count, starts, length, mul_assoc] using hbridge
  calc
    _ ≤ iidSequenceLaw ν
        (⋃ j : Fin (count n),
          RandomWalk.twoOrderedBlockExcursions (starts n j) (length n)
            (ε * normalization n)) := measure_mono hbadSubset
    _ ≤ (count n : ENNReal) *
        (ENNReal.ofReal
          (blockFraction * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2))) ^ 2 := by
      have hthresholdEq : 2 * (ε / 2 * normalization n) = ε * normalization n := by
        ring
      simpa [count, starts, length, hthresholdEq] using hlocalN

/-- Endpoint failures are controlled by two one-block stable estimates, one
at each end of the sample. The pathwise inclusion comes from the generic
endpoint criterion bridge. The estimate is separate from the double-
excursion bound because Billingsley's converse requires both controls. -/
theorem eventually_measure_not_hasEndpointOscillationBound_le_of_stableNorming
    {α radiusMultiplier ε endpointDelta blockFraction : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hε : 0 < ε)
    (hblockFraction : 0 ≤ blockFraction)
    (width : ℕ → ℕ) (hwidth : ∀ n, 0 < width n)
    (hwidthLower : ∀ᶠ n : ℕ in atTop, (n : ℝ) * endpointDelta ≤ width n)
    (hlengthRatio : ∀ᶠ n : ℕ in atTop, (width n : ℝ) / n ≤ blockFraction)
    (hbias : ∀ᶠ n : ℕ in atTop,
      (width n : ℝ) *
        |truncatedIncrementMean ν (radiusMultiplier * normalization n)| /
          normalization n ≤ ε / 4) :
    ∀ᶠ n in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasEndpointOscillationBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤
        2 * ENNReal.ofReal
          (blockFraction * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
            4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2)) := by
  have hblock := eventually_measure_blockPrefixExceedance_le_of_stableNorming_unitMargins
    (thresholdMultiplier := ε / 2)
    hnorm hα₀ hα₂ htail hradius (by positivity) hblockFraction width
      (Filter.Eventually.of_forall hwidth) hlengthRatio (by
        filter_upwards [hbias] with n hn
        calc
          _ ≤ ε / 4 := hn
          _ = (ε / 2) / 2 := by ring)
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  filter_upwards [hblock, hscale, hwidthLower, eventually_gt_atTop (0 : ℕ)] with
      n hblockN hscaleN hwidthLowerN hn
  let threshold : ℝ := (ε / 2) * normalization n
  let bound : ENNReal := ENNReal.ofReal
    (blockFraction * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
      4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2))
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    exact mul_pos (by positivity) hscaleN
  have hbound : iidSequenceLaw ν
      (blockPrefixExceedance 0 (width n) threshold) ≤ bound := by
    simpa [threshold, bound] using hblockN
  have htailBlock : iidSequenceLaw ν
      (blockPrefixExceedance (n - width n) (width n) threshold) ≤ bound := by
    calc
      _ = iidSequenceLaw ν (blockPrefixExceedance
          (n - width n + 0) (width n) threshold) := by simp
      _ = iidSequenceLaw ν (blockPrefixExceedance 0 (width n) threshold) :=
        RandomWalk.measure_blockPrefixExceedance_translate_eq ν
          (n - width n) 0 (width n) threshold
      _ ≤ bound := hbound
  have hbridgeSubset :
      {increment | ¬ Skorokhod.HasEndpointOscillationBound
        (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
        endpointDelta ε} ⊆
        blockPrefixExceedance 0 (width n) (ε * normalization n / 2) ∪
          blockPrefixExceedance (n - width n) (width n)
            (ε * normalization n / 2) := by
    intro increment hbad
    exact RandomWalk.normalizedStepCadlagPathIcc_not_hasEndpointOscillationBound_subset_boundaryBlocks
      normalization n (by omega) hscaleN endpointDelta ε hε (width n)
      hwidthLowerN increment hbad
  have hthresholdEq : threshold = ε * normalization n / 2 := by
    dsimp [threshold]
    ring
  have hfirst : iidSequenceLaw ν
      (blockPrefixExceedance 0 (width n) (ε * normalization n / 2)) ≤ bound := by
    simpa [hthresholdEq] using hbound
  have hlast : iidSequenceLaw ν
      (blockPrefixExceedance (n - width n) (width n)
        (ε * normalization n / 2)) ≤ bound := by
    simpa [hthresholdEq] using htailBlock
  calc
    _ ≤ iidSequenceLaw ν
        (blockPrefixExceedance 0 (width n) (ε * normalization n / 2) ∪
          blockPrefixExceedance (n - width n) (width n)
            (ε * normalization n / 2)) := measure_mono hbridgeSubset
    _ ≤ iidSequenceLaw ν
        (blockPrefixExceedance 0 (width n) (ε * normalization n / 2)) +
          iidSequenceLaw ν (blockPrefixExceedance (n - width n) (width n)
            (ε * normalization n / 2)) := measure_union_le _ _
    _ ≤ bound + bound := add_le_add hfirst hlast
    _ = 2 * bound := by simp [two_mul]
    _ = 2 * ENNReal.ofReal
        (blockFraction * (((2 - α) / α) * radiusMultiplier ^ (-α) + 1 +
          4 * (radiusMultiplier ^ (2 - α) + 1) / (ε / 2) ^ 2)) := by
      rfl

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.FirstCrossing
public import Probability.Process.RandomWalk.Path.Skorokhod.Oscillation

/-!
# Block bounds for Skorokhod oscillation criteria

This module converts a one-block random-walk maximal bound into the double-
excursion and endpoint estimates used by the deterministic Skorokhod
compactness criterion. Distribution-specific tail or moment estimates belong
in adapters above this layer.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit

/-- A one-block prefix-excursion bound gives a squared bound for two ordered
excursions in the same block. The first crossing separates the two events,
so the second estimate uses fresh independent increments. -/
theorem eventually_measure_twoOrderedBlockExcursions_le_of_blockPrefixBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (normalization : ℕ → ℝ) {thresholdMultiplier : ℝ}
    (hthreshold : 0 < thresholdMultiplier) (bound : ℝ≥0∞)
    {start length : ℕ → ℕ}
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n)
    (hblock : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance 0 (length n)
          (thresholdMultiplier * normalization n)) ≤ bound) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (RandomWalk.twoOrderedBlockExcursions (start n) (length n)
          (2 * (thresholdMultiplier * normalization n))) ≤ bound ^ 2 := by
  filter_upwards [hblock, hscale] with n hblockN hscaleN
  have hblockN' : iidSequenceLaw ν
      (blockPrefixExceedance 0 (length n)
        (thresholdMultiplier * normalization n)) ≤ bound := hblockN
  have hthresholdN : 0 < thresholdMultiplier * normalization n :=
    mul_pos hthreshold hscaleN
  calc
    _ = (iidSequenceLaw ν)
        (RandomWalk.twoOrderedPrefixExcursions (length n)
          (2 * (thresholdMultiplier * normalization n))) :=
      RandomWalk.measure_twoOrderedBlockExcursions_translate_eq ν
        (start n) (length n) _
    _ ≤ bound ^ 2 :=
      RandomWalk.measure_twoOrderedPrefixExcursions_le_sq_of_blockBound
        ν (length n) hthresholdN bound hblockN'

/-- A bound on one block controls the probability that a normalized
right-continuous random-walk path violates Billingsley's double-excursion
condition. The deterministic window cover has `n / width + 1` blocks. -/
theorem eventually_measure_not_hasDoubleExcursionBound_le_of_blockPrefixBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} {ε endpointDelta : ℝ}
    (hε : 0 < ε)
    (bound : ℝ≥0∞) (hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n)
    (width : ℕ → ℕ) (hwidth : ∀ n, 0 < width n)
    (hwidthLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * endpointDelta ≤ width n)
    (hblock : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance 0 (2 * width n)
          (ε * normalization n / 2)) ≤ bound) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasDoubleExcursionBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤
        ((n / width n + 1 : ℕ) : ℝ≥0∞) * bound ^ 2 := by
  let count : ℕ → ℕ := fun n => n / width n + 1
  let starts : ∀ n, Fin (count n) → ℕ := fun n j => j.val * width n
  have hlocal : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (⋃ j : Fin (count n),
          RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
            (ε * normalization n)) ≤ (count n : ENNReal) * bound ^ 2 := by
    filter_upwards [hblock, hscale] with n hblockN hscaleN
    have hthreshold : 0 < (ε / 2) * normalization n :=
      mul_pos (by positivity) hscaleN
    have hprefix : iidSequenceLaw ν
        (blockPrefixExceedance 0 (2 * width n)
          ((ε / 2) * normalization n)) ≤ bound := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hblockN
    have hwindow (j : Fin (count n)) :
        iidSequenceLaw ν
          (RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
            (ε * normalization n)) ≤ bound ^ 2 := by
      have hbound := RandomWalk.measure_twoOrderedPrefixExcursions_le_sq_of_blockBound
        ν (2 * width n) hthreshold bound hprefix
      have hthresholdEq : 2 * ((ε / 2) * normalization n) =
          ε * normalization n := by ring
      calc
        _ = iidSequenceLaw ν
            (RandomWalk.twoOrderedPrefixExcursions (2 * width n)
              (ε * normalization n)) :=
          RandomWalk.measure_twoOrderedBlockExcursions_translate_eq ν
            (starts n j) (2 * width n) _
        _ ≤ bound ^ 2 := by simpa [hthresholdEq] using hbound
    calc
      _ ≤ ∑' j : Fin (count n),
          iidSequenceLaw ν
            (RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
              (ε * normalization n)) := measure_iUnion_le _
      _ = ∑ j : Fin (count n),
          iidSequenceLaw ν
            (RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
              (ε * normalization n)) := by simp only [tsum_fintype]
      _ ≤ ∑ j : Fin (count n), bound ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hwindow j
      _ = (count n : ENNReal) * bound ^ 2 := by simp
  have hscale' : ∀ᶠ n : ℕ in atTop, 0 < normalization n := hscale
  filter_upwards [hlocal, hscale', hwidthLower,
    eventually_gt_atTop (0 : ℕ)] with n hlocalN hscaleN hwidthLowerN hn
  have hbadSubset :
      {increment | ¬ Skorokhod.HasDoubleExcursionBound
        (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
        endpointDelta ε} ⊆
      ⋃ j : Fin (count n),
        RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
          (ε * normalization n) := by
    intro increment hbad
    have hbridge := RandomWalk.normalizedStepCadlagPathIcc_not_hasDoubleExcursionBound_subset_windowGrid
      normalization n (by omega) hscaleN endpointDelta ε (width n) (hwidth n)
      hwidthLowerN increment hbad
    simpa [count, starts, mul_assoc] using hbridge
  calc
    _ ≤ iidSequenceLaw ν
        (⋃ j : Fin (count n),
          RandomWalk.twoOrderedBlockExcursions (starts n j) (2 * width n)
            (ε * normalization n)) := measure_mono hbadSubset
    _ ≤ (count n : ENNReal) * bound ^ 2 := hlocalN

/-- A one-block prefix-excursion bound controls both endpoint failures in
Billingsley's endpoint oscillation condition. -/
theorem eventually_measure_not_hasEndpointOscillationBound_le_of_blockPrefixBound
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} {ε endpointDelta : ℝ}
    (hε : 0 < ε)
    (bound : ℝ≥0∞) (hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n)
    (width : ℕ → ℕ)
    (hwidthLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * endpointDelta ≤ width n)
    (hblock : ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance 0 (width n)
          (ε * normalization n / 2)) ≤ bound) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν
        {increment | ¬ Skorokhod.HasEndpointOscillationBound
          (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
          endpointDelta ε} ≤ 2 * bound := by
  filter_upwards [hblock, hscale, hwidthLower,
    eventually_gt_atTop (0 : ℕ)] with n hblockN hscaleN hwidthLowerN hn
  have hthreshold : 0 < (ε / 2) * normalization n :=
    mul_pos (by positivity) hscaleN
  have hprefix : iidSequenceLaw ν
      (blockPrefixExceedance 0 (width n)
        ((ε / 2) * normalization n)) ≤ bound := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hblockN
  have htailBlock : iidSequenceLaw ν
      (blockPrefixExceedance (n - width n) (width n)
        ((ε / 2) * normalization n)) ≤ bound := by
    calc
      _ = iidSequenceLaw ν (blockPrefixExceedance
          (n - width n + 0) (width n) ((ε / 2) * normalization n)) := by simp
      _ = iidSequenceLaw ν
          (blockPrefixExceedance 0 (width n) ((ε / 2) * normalization n)) :=
        RandomWalk.measure_blockPrefixExceedance_translate_eq ν
          (n - width n) 0 (width n) ((ε / 2) * normalization n)
      _ ≤ bound := hprefix
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
  have hthresholdEq : (ε / 2) * normalization n =
      ε * normalization n / 2 := by ring
  have hfirst : iidSequenceLaw ν
      (blockPrefixExceedance 0 (width n) (ε * normalization n / 2)) ≤ bound := by
    simpa [hthresholdEq] using hprefix
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

end ProbabilityTheory.RandomWalk.FunctionalLimit

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.Path.Block.Law.Excursions
import Probability.Process.RandomWalk.Path.Truncation.AdjacentBlocks

/-!
# Independent adjacent increment-block excursion API checks
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (leftThreshold rightThreshold : ℝ) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance start length leftThreshold ∩
          blockPrefixExceedance (start + length) length rightThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start length leftThreshold) *
        (iidSequenceLaw ν) (blockPrefixExceedance (start + length) length rightThreshold) :=
  measure_inter_adjacentBlockPrefixExceedance_eq_mul
    ν start length leftThreshold rightThreshold

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start leftLength rightLength : ℕ) (leftThreshold rightThreshold : ℝ) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance start leftLength leftThreshold ∩
          blockPrefixExceedance (start + leftLength) rightLength rightThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start leftLength leftThreshold) *
        (iidSequenceLaw ν)
          (blockPrefixExceedance (start + leftLength) rightLength rightThreshold) :=
  measure_inter_adjacentBlockPrefixExceedance_eq_mul_of_lengths
    ν start leftLength rightLength leftThreshold rightThreshold

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (shift start length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedance (shift + start) length threshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) :=
  measure_blockPrefixExceedance_translate_eq ν shift start length threshold

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ → ℕ) (threshold : ℕ → ℝ) (bound : ℕ → ENNReal)
    (hbound : ∀ᶠ n : ℕ in Filter.atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n) (length n) (threshold n)) ≤ bound n) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n) (length n) (threshold n) ∩
          blockPrefixExceedance (start n + length n) (length n) (threshold n)) ≤
        bound n ^ 2 :=
  eventually_measure_inter_adjacentBlockPrefixExceedance_le_sq_of_oneBlockBound
    ν start length threshold bound hbound

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) (leftThreshold rightThreshold : ℝ)
    (leftBound rightBound : ENNReal)
    (hleft : (iidSequenceLaw ν)
      (blockPrefixExceedance start length leftThreshold) ≤ leftBound)
    (hright : (iidSequenceLaw ν)
      (blockPrefixExceedance (start + length) length rightThreshold) ≤ rightBound) :
    (iidSequenceLaw ν)
      (blockPrefixExceedance start length leftThreshold ∩
        blockPrefixExceedance (start + length) length rightThreshold) ≤
      leftBound * rightBound :=
  measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds ν start length
    leftThreshold rightThreshold leftBound rightBound hleft hright

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start : Fin count → ℕ) (length : ℕ)
    (threshold : ℝ) (bound : ENNReal)
    (hbound : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j) length threshold) ≤ bound) :
    (iidSequenceLaw ν)
      (⋃ j : Fin count,
        blockPrefixExceedance (start j) length threshold ∩
          blockPrefixExceedance (start j + length) length threshold) ≤
      (count : ENNReal) * bound ^ 2 :=
  measure_iUnion_adjacentBlockPrefixExceedance_le_of_commonBound
    ν start length threshold bound hbound

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start leftLength rightLength : Fin count → ℕ)
    (leftThreshold rightThreshold : ℝ)
    (leftBound rightBound : Fin count → ENNReal)
    (hleft : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j) (leftLength j) leftThreshold) ≤ leftBound j)
    (hright : ∀ j, (iidSequenceLaw ν)
      (blockPrefixExceedance (start j + leftLength j) (rightLength j)
        rightThreshold) ≤ rightBound j) :
    (iidSequenceLaw ν)
      (⋃ j : Fin count,
        blockPrefixExceedance (start j) (leftLength j) leftThreshold ∩
          blockPrefixExceedance (start j + leftLength j) (rightLength j)
            rightThreshold) ≤
      ∑ j : Fin count, leftBound j * rightBound j :=
  measure_iUnion_adjacentBlockPrefixExceedance_le_of_bounds ν start leftLength
    rightLength leftThreshold rightThreshold leftBound rightBound hleft hright

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {count : ℕ} (start leftLength rightLength : ℕ → Fin count → ℕ)
    (leftThreshold rightThreshold : ℕ → ℝ)
    (leftBound rightBound : ℕ → Fin count → ENNReal)
    (hleft : ∀ᶠ n in atTop, ∀ j,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n j) (leftLength n j)
          (leftThreshold n)) ≤ leftBound n j)
    (hright : ∀ᶠ n in atTop, ∀ j,
      (iidSequenceLaw ν)
        (blockPrefixExceedance (start n j + leftLength n j) (rightLength n j)
          (rightThreshold n)) ≤ rightBound n j) :
    ∀ᶠ n in atTop,
      (iidSequenceLaw ν)
        (⋃ j : Fin count,
          blockPrefixExceedance (start n j) (leftLength n j)
              (leftThreshold n) ∩
            blockPrefixExceedance (start n j + leftLength n j)
              (rightLength n j) (rightThreshold n)) ≤
        ∑ j : Fin count, leftBound n j * rightBound n j :=
  eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_eventually_bounds
    ν start leftLength rightLength leftThreshold rightThreshold leftBound rightBound
    hleft hright

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {center radius threshold : ℝ} (length : ℕ) (hlength : 0 < length)
    (hgap : (length : ℝ) *
      |truncatedIncrementMean (ν.map (fun x : ℝ => x - center)) radius| < threshold) :
    (iidSequenceLaw (ν.map (fun x : ℝ => x - center)))
        (blockPrefixExceedance 0 length threshold ∩
          blockPrefixExceedance length length threshold) ≤
      (((length : ℕ) * ν {x | radius < |x - center|}) +
        truncatedCenteredSecondBound
          (ν.map (fun x : ℝ => x - center)) radius (length - 1)
          (threshold - (length : ℝ) *
            |truncatedIncrementMean (ν.map (fun x : ℝ => x - center)) radius|)) ^ 2 :=
  measure_inter_adjacentBlockPrefixExceedance_le_sq_of_truncation_second_bounded
    ν length hlength hgap

#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_eq_mul
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_eq_mul_of_lengths
#print axioms ProbabilityTheory.RandomWalk.measure_blockPrefixExceedance_translate_eq
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds_of_lengths
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound
#print axioms ProbabilityTheory.RandomWalk.measure_iUnion_adjacentBlockPrefixExceedance_le_of_commonBound
#print axioms ProbabilityTheory.RandomWalk.measure_iUnion_adjacentBlockPrefixExceedance_le_of_bounds
#print axioms ProbabilityTheory.RandomWalk.eventually_measure_iUnion_adjacentBlockPrefixExceedance_le_of_eventually_bounds
#print axioms ProbabilityTheory.RandomWalk.eventually_measure_inter_adjacentBlockPrefixExceedance_le_sq_of_oneBlockBound
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_truncation_second_bounded

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
    (start length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedance (length + start) length threshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) :=
  measure_blockPrefixExceedance_shift_eq ν start length threshold

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
#print axioms ProbabilityTheory.RandomWalk.measure_blockPrefixExceedance_shift_eq
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_mul_of_bounds
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound
#print axioms ProbabilityTheory.RandomWalk.eventually_measure_inter_adjacentBlockPrefixExceedance_le_sq_of_oneBlockBound
#print axioms ProbabilityTheory.RandomWalk.measure_inter_adjacentBlockPrefixExceedance_le_sq_of_truncation_second_bounded

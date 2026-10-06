/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.Path.Block.Law.FirstCrossing

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (incrementFiltration (E := ℝ)) τ)
    (length : ℕ) (threshold : ℝ) :
    (iidSequenceLaw ν) (blockPrefixExceedanceAfter τ length threshold) ≤
      (iidSequenceLaw ν) (blockPrefixExceedance 0 length threshold) :=
  measure_blockPrefixExceedanceAfter_le ν τ hτ length threshold

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (τ : (ℕ → ℝ) → WithTop ℕ)
    (hτ : IsStoppingTime (incrementFiltration (E := ℝ)) τ)
    (length : ℕ) (threshold : ℝ) (start : ℕ) :
    (iidSequenceLaw ν)
        (blockPrefixExceedanceAfter τ length threshold) ≤
      (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) := by
  calc
    _ ≤ (iidSequenceLaw ν) (blockPrefixExceedance 0 length threshold) :=
      measure_blockPrefixExceedanceAfter_le ν τ hτ length threshold
    _ = (iidSequenceLaw ν) (blockPrefixExceedance start length threshold) := by
      symm
      exact measure_blockPrefixExceedance_translate_eq ν start 0 length threshold

#print axioms ProbabilityTheory.RandomWalk.measure_stoppingTimeCell_inter_blockPrefixExceedance_eq_mul
#print axioms ProbabilityTheory.RandomWalk.measure_blockPrefixExceedanceAfter_le
#print axioms ProbabilityTheory.iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
#print axioms ProbabilityTheory.iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul
#print axioms ProbabilityTheory.RandomWalk.firstPrefixExceedanceTime_isStoppingTime
#print axioms ProbabilityTheory.RandomWalk.measure_inter_boundedStoppingTime_blockPrefixExceedanceAfter_eq_mul
#print axioms ProbabilityTheory.RandomWalk.measure_firstPrefixExceedance_and_postCrossingBlockPrefixExceedance_eq_mul

example (threshold : ℝ) :
    IsStoppingTime (incrementFiltration (E := ℝ))
      (firstPrefixExceedanceTime threshold) :=
  firstPrefixExceedanceTime_isStoppingTime threshold

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (firstLength futureLength : ℕ) (firstThreshold futureThreshold : ℝ)
    (hfirstThreshold : 0 < firstThreshold) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance 0 firstLength firstThreshold ∩
          blockPrefixExceedanceAfter (firstPrefixExceedanceTime firstThreshold)
            futureLength futureThreshold) =
      (iidSequenceLaw ν) (blockPrefixExceedance 0 firstLength firstThreshold) *
        (iidSequenceLaw ν) (blockPrefixExceedance 0 futureLength futureThreshold) :=
  measure_firstPrefixExceedance_and_postCrossingBlockPrefixExceedance_eq_mul
    ν firstLength futureLength firstThreshold futureThreshold hfirstThreshold

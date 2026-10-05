/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.Path.Truncation.Maximal.SecondMoment

/-!
# Infinite-variance truncation estimate API checks

These checks ensure the second-moment truncation estimate requires no global
second moment of the original increment law and introduces no project axioms.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk

example (ν : Measure ℝ) [IsProbabilityMeasure ν] (radius : ℝ) :
    (∫ x, truncatedIncrement radius x ^ 2 ∂ν) =
      truncatedSecondMoment ν radius :=
  integral_truncatedIncrement_sq_eq_truncatedSecondMoment ν radius

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {radius threshold : ℝ} (blocks length : ℕ)
    (hgap : ((length + 1 : ℕ) : ℝ) *
      |truncatedIncrementMean ν radius| < threshold) :
    (iidSequenceLaw ν) {path |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ≤
      ((blocks * length + 1 : ℕ) * ν {x | radius < |x|}) +
        (blocks : ℕ) * truncatedCenteredSecondBound ν radius length
          (threshold - ((length + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν radius|) :=
  measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded
    ν blocks length hgap

#print axioms ProbabilityTheory.RandomWalk.integral_truncatedIncrement_sq_eq_truncatedSecondMoment
#print axioms ProbabilityTheory.RandomWalk.maximal_ineq_sq_blockSum_centeredTruncated_bounded
#print axioms ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded

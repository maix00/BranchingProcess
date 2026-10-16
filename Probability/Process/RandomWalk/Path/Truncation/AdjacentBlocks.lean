/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Law.Excursions
public import Probability.Process.RandomWalk.Path.Truncation.Maximal.SecondMoment

/-!
# Adjacent-block probability bounds for truncated walks

The increment center is explicit. The two prefix events use disjoint blocks,
so their intersection is bounded by the square of the one-block truncation
bound. All moment and tail terms are computed under the same shifted law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Two adjacent blocks both have a large partial sum with probability at most
the square of the one-block hard-truncation bound. The block length counts
increments exactly, and the center is an explicit one-step shift. -/
theorem measure_inter_adjacentBlockPrefixExceedance_le_sq_of_truncation_second_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
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
            |truncatedIncrementMean (ν.map (fun x : ℝ => x - center)) radius|)) ^ 2 := by
  let shifted : Measure ℝ := ν.map (fun x : ℝ => x - center)
  let μ := iidSequenceLaw shifted
  let tailTerm : ENNReal :=
    (length : ℕ) * ν {x | radius < |x - center|}
  let centeredMean : ℝ := truncatedIncrementMean shifted radius
  let varianceTerm : ENNReal :=
    truncatedCenteredSecondBound shifted radius (length - 1)
      (threshold - (length : ℝ) * |centeredMean|)
  let bound : ENNReal := tailTerm + varianceTerm
  have hlength' : length - 1 + 1 = length := by omega
  have hgap' : (((length - 1 + 1 : ℕ) : ℝ) * |centeredMean| < threshold) := by
    simpa [centeredMean, hlength'] using hgap
  have hsingleSubset : blockPrefixExceedance 0 length threshold ⊆
      {path : ℕ → ℝ | ∃ j < 1, ∃ k ∈ Finset.range ((length - 1) + 1),
        threshold ≤ |AdditivePath.blockSum (j * (length - 1)) (k + 1) path|} := by
    intro path hpath
    obtain ⟨k, hk⟩ := hpath
    refine ⟨0, by omega, k.val, ?_, ?_⟩
    · exact Finset.mem_range.2 (by omega)
    · simpa using hk
  have hsingle := measure_exists_block_exists_abs_ge_le_of_truncation_second_bounded
    shifted 1 (length - 1) hgap'
  have htail : shifted {y : ℝ | radius < |y|} =
      ν {x : ℝ | radius < |x - center|} := by
    change (ν.map (fun x : ℝ => x - center)) {y : ℝ | radius < |y|} = _
    rw [Measure.map_apply (show Measurable (fun x : ℝ => x - center) by fun_prop)
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    congr 1
  have hsingleBound : μ (blockPrefixExceedance 0 length threshold) ≤ bound := by
    calc
      _ ≤ μ {path : ℕ → ℝ |
          ∃ j < 1, ∃ k ∈ Finset.range ((length - 1) + 1),
            threshold ≤ |AdditivePath.blockSum (j * (length - 1)) (k + 1) path|} :=
        measure_mono hsingleSubset
      _ ≤ bound := by
        simpa [μ, shifted, bound, tailTerm, varianceTerm, centeredMean,
          hlength', Nat.one_mul, htail] using hsingle
  simpa [μ, shifted, bound, tailTerm, varianceTerm, centeredMean,
    Nat.zero_add] using
    (measure_inter_adjacentBlockPrefixExceedance_le_sq_of_bound
      shifted 0 length threshold bound (by simpa [μ] using hsingleBound))

end ProbabilityTheory.RandomWalk

end

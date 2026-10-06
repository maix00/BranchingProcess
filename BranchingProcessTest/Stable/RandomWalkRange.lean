/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathRange

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

example {α ε : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hε : 0 < ε) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (ProbabilityTheory.RandomWalk.normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε :=
  exists_eventually_compactRange_bound_of_index_lt_one
    hnorm hα₀ hα₁ htail hε

example {α radiusMultiplier thresholdMultiplier tailBound momentBound : ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hradius : 0 < radiusMultiplier) (hthreshold : 0 < thresholdMultiplier)
    (htailBound : ((2 - α) / α) * radiusMultiplier ^ (-α) < tailBound)
    (hmomentBound : radiusMultiplier ^ (2 - α) < momentBound)
    (hbias : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) *
        |ProbabilityTheory.RandomWalk.truncatedIncrementMean ν
          (radiusMultiplier * normalization n)| / normalization n ≤
            thresholdMultiplier / 2) :
    ∀ᶠ n : ℕ in atTop,
      (ProbabilityTheory.RandomWalk.normalizedStepPathLaw ν normalization n)
        (CadlagPath.rangeIn (T := unitInterval)
          (Set.Icc (-thresholdMultiplier) thresholdMultiplier))ᶜ ≤
        ENNReal.ofReal (tailBound + 4 * momentBound / thresholdMultiplier ^ 2) :=
  eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming
    hnorm hα₀ hα₂ htail hradius hthreshold htailBound hmomentBound hbias

#print axioms ProbabilityTheory.RandomWalk.not_mem_rangeIn_closedInterval_subset_blockPrefixExceedance
#print axioms ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_mem_rangeIn_closedInterval_iff_partialSumBounds
#print axioms ProbabilityTheory.RandomWalk.measure_normalizedStepPathLaw_rangeIn_closedInterval_compl_le_of_blockPrefixExceedance
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_blockPrefixExceedance_le_of_stableNorming
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.eventually_measure_normalizedStepPathLaw_rangeExit_le_of_stableNorming
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_lt_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_gt_one
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_lt_one_ennreal
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_one_ennreal
#print axioms ProbabilityTheory.RandomWalk.FunctionalLimit.Stable.exists_eventually_compactRange_bound_of_index_gt_one_ennreal

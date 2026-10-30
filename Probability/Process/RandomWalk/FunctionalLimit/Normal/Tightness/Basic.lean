/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import MeasureTheory.Measure.CadlagPath.Tightness
public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Process.RandomWalk.Path.Truncation.Normalized
public import Probability.Process.RandomWalk.Path.Skorokhod.Tightness
import all Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness.Lemmas.CompactRange
import all Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness.Lemmas.OscillationPartitions

/-!
# J₁ tightness in the normal domain of attraction

The normal-domain compact-range and oscillation-partition estimates combine
through the general càdlàg Skorokhod tightness criterion. This includes the
infinite-variance normal domain of attraction.
## Public declarations

- `isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian` proves that the
  family of normalized càdlàg step-path laws is tight in the Skorokhod $J_1$
  topology throughout the centered Gaussian domain of attraction, including
  source laws with infinite variance.

-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

/-- The normalized càdlàg random-walk path laws are tight in the (J_1)
topology throughout the Gaussian domain of attraction, with no finite-second-
moment assumption. -/
theorem isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (h : IsInDomainOfAttractionAlong ν
      (gaussianReal 0 1) normalization (fun _ => 0))
    (hnormalization : ∀ n, 0 < n → 0 < normalization n) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedStepPathLaw ν normalization n)) := by
  apply MeasureTheory.isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions
  · intro n
    exact RandomWalk.isTightMeasureSet_singleton_normalizedStepPathLaw ν normalization n
  · intro η hη
    exact MeasureTheory.exists_eventually_compactRange_bound_of_real_error
      (μ := fun n => normalizedStepPathLaw ν normalization n)
      (fun ε hε => exists_eventually_compactRange_bound_of_gaussian
        h hnormalization hε) hη
  · intro η hη
    let η' := min η (1 / 2 : ℝ≥0∞)
    have hη' : 0 < η' := by
      dsimp [η']
      exact lt_min hη (by norm_num)
    have hη'one : η' < 1 := by
      dsimp [η']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨gap, tolerance, hgap, htolerance, htendsto, hmass⟩ :=
      exists_eventually_oscillationPartitions_bound_of_gaussian
        h hnormalization hη' hη'one
    refine ⟨gap, tolerance, hgap, htolerance, htendsto, ?_⟩
    filter_upwards [hmass] with n hn
    exact hn.trans (min_le_left _ _)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

end

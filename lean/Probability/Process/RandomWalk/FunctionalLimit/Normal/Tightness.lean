/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.OscillationPartitions
public import Probability.Process.RandomWalk.FunctionalLimit.Normal.PathRange
public import Probability.Process.RandomWalk.Path.Skorokhod.Tightness

/-!
# J₁ tightness in the normal domain of attraction

The normal-domain compact-range and oscillation-partition estimates combine
through the general càdlàg Skorokhod tightness criterion. This includes the
infinite-variance normal domain of attraction.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Normal

private theorem exists_eventually_compactRange_bound_of_ennrealBudget
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (normalization : ℕ → ℝ)
    (hreal : ∀ ε : ℝ, 0 < ε →
      ∃ range : Set ℝ, IsCompact range ∧
        ∀ᶠ n : ℕ in atTop,
          (normalizedStepPathLaw ν normalization n)
            (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ ENNReal.ofReal ε)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ range : Set ℝ, IsCompact range ∧
      ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η := by
  by_cases htop : η = ⊤
  · refine ⟨Set.Icc (-1 : ℝ) 1, isCompact_Icc, ?_⟩
    filter_upwards with n
    calc
      (normalizedStepPathLaw ν normalization n)
          (CadlagPath.rangeIn (T := unitInterval) (Set.Icc (-1 : ℝ) 1))ᶜ ≤ 1 := by
        calc
          _ ≤ normalizedStepPathLaw ν normalization n Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := by simp
      _ ≤ η := by rw [htop]; exact le_top
  · have hηreal : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) htop
    obtain ⟨range, hrange, hmass⟩ := hreal η.toReal hηreal
    refine ⟨range, hrange, ?_⟩
    filter_upwards [hmass] with n hn
    rwa [ENNReal.ofReal_toReal htop] at hn

private theorem isTightMeasureSet_range_normalizedStepPathLaw_of_pathBounds
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (normalization : ℕ → ℝ)
    (hrange : ∀ {η : ℝ≥0∞}, 0 < η →
      ∃ range : Set ℝ, IsCompact range ∧
        ∀ᶠ n : ℕ in atTop,
          (normalizedStepPathLaw ν normalization n)
            (CadlagPath.rangeIn (T := unitInterval) range)ᶜ ≤ η)
    (hosc : ∀ {η : ℝ≥0∞}, 0 < η →
      ∃ gap oscillationTolerance : ℕ → ℝ,
        (∀ n, 0 < gap n) ∧ (∀ n, 0 < oscillationTolerance n) ∧
          Tendsto oscillationTolerance atTop (nhds 0) ∧
            ∀ᶠ n : ℕ in atTop,
              (normalizedStepPathLaw ν normalization n)
                (Skorokhod.admitsOscillationPartitionSequence
                  (E := ℝ) gap oscillationTolerance)ᶜ ≤ η) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedStepPathLaw ν normalization n)) := by
  apply MeasureTheory.isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions
  · intro n
    exact RandomWalk.isTightMeasureSet_singleton_normalizedStepPathLaw ν normalization n
  · exact hrange
  · exact hosc

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
  apply isTightMeasureSet_range_normalizedStepPathLaw_of_pathBounds ν normalization
  · intro η hη
    apply exists_eventually_compactRange_bound_of_ennrealBudget ν normalization
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

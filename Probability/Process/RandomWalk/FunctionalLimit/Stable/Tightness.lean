/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Tightness.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.OscillationPartitions
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathRange
public import Probability.Process.RandomWalk.Path.Skorokhod.Tightness

/-!
# Stable random-walk path tightness

The stable excursion-partition probability bounds and compact-range bounds
combine through the general Skorokhod criterion to prove J1 tightness.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- The stable oscillation-partition estimate and compact-range control imply
J1 tightness for the whole family of normalized càdlàg random-walk path laws.
The three source centering conventions are kept separate in the corollaries
below. -/
private theorem isTightMeasureSet_range_normalizedStepPathLaw_of_range_and_oscillation
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
  apply Process.Path.isTightMeasureSet_range_of_eventually_compactRange_and_oscillationPartitions
  · intro n
    exact RandomWalk.isTightMeasureSet_singleton_normalizedStepPathLaw ν normalization n
  · exact hrange
  · exact hosc

/-- The stable random-walk path laws are J1-tight below index one under the
uncentered stable-domain convention. -/
theorem isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedStepPathLaw ν normalization n)) := by
  apply isTightMeasureSet_range_normalizedStepPathLaw_of_range_and_oscillation
    ν normalization
  · intro η hη
    exact exists_eventually_compactRange_bound_of_index_lt_one_ennreal
      hnorm hα₀ hα₁ htail hη
  · intro η hη
    let η' := min η (1 / 2 : ℝ≥0∞)
    have hη' : 0 < η' := by
      dsimp [η']
      exact lt_min hη (by norm_num)
    have hη'one : η' < 1 := by
      dsimp [η']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨gap, tolerance, hgap, htolerance, htendsto, hmass⟩ :=
      exists_eventually_oscillationPartitions_bound_of_index_lt_one
        hnorm hα₀ hα₁ htail hη' hη'one
    refine ⟨gap, tolerance, hgap, htolerance, htendsto, ?_⟩
    filter_upwards [hmass] with n hn
    exact hn.trans (min_le_left _ _)

/-- The stable random-walk path laws are J1-tight at index one under the
sine-centering convention. -/
theorem isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedStepPathLaw ν normalization n)) := by
  apply isTightMeasureSet_range_normalizedStepPathLaw_of_range_and_oscillation
    ν normalization
  · intro η hη
    exact exists_eventually_compactRange_bound_of_index_one_ennreal
      hnorm htail hcenter hη
  · intro η hη
    let η' := min η (1 / 2 : ℝ≥0∞)
    have hη' : 0 < η' := by
      dsimp [η']
      exact lt_min hη (by norm_num)
    have hη'one : η' < 1 := by
      dsimp [η']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨gap, tolerance, hgap, htolerance, htendsto, hmass⟩ :=
      exists_eventually_oscillationPartitions_bound_of_index_one
        hnorm htail hcenter hη' hη'one
    refine ⟨gap, tolerance, hgap, htolerance, htendsto, ?_⟩
    filter_upwards [hmass] with n hn
    exact hn.trans (min_le_left _ _)

/-- The stable random-walk path laws are J1-tight above index one under
integrable centered increments. -/
theorem isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ} (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hint : Integrable (fun x : ℝ => x) ν)
    (hcenter : (∫ x : ℝ, x ∂ν) = 0) :
    IsTightMeasureSet (Set.range
      (fun n => normalizedStepPathLaw ν normalization n)) := by
  apply isTightMeasureSet_range_normalizedStepPathLaw_of_range_and_oscillation
    ν normalization
  · intro η hη
    exact exists_eventually_compactRange_bound_of_index_gt_one_ennreal
      hnorm hα₀ hα₁ hα₂ htail hint hcenter hη
  · intro η hη
    let η' := min η (1 / 2 : ℝ≥0∞)
    have hη' : 0 < η' := by
      dsimp [η']
      exact lt_min hη (by norm_num)
    have hη'one : η' < 1 := by
      dsimp [η']
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨gap, tolerance, hgap, htolerance, htendsto, hmass⟩ :=
      exists_eventually_oscillationPartitions_bound_of_index_gt_one
        hnorm hα₀ hα₁ hα₂ htail hint hcenter hη' hη'one
    refine ⟨gap, tolerance, hgap, htolerance, htendsto, ?_⟩
    filter_upwards [hmass] with n hn
    exact hn.trans (min_le_left _ _)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end

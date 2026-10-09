/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.MeasurableSpace.ContinuousMap.Oscillation
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Topology.ContinuousMap.Oscillation

/-!
# Continuous-path oscillation bounds for measures

-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.ContinuousMap

/-- A path law concentrated on paths starting at zero assigns to the
range-oscillation set at most the sum of the fixed finite corridor cover. -/
theorem measure_rangeOscillationSet_le_finiteCorridorCover
    (μ : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure μ]
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count)
    (hstart : ∀ᵐ path ∂μ, path 0 = 0) :
    μ (ContinuousMap.rangeOscillationSet width) ≤
      ∑ j : Fin count,
        μ (ContinuousMap.rangeInOpenInterval
          (ContinuousMap.oscillationCoverLower width count j)
          (ContinuousMap.oscillationCoverUpper width count j)) := by
  let osc := ContinuousMap.rangeOscillationSet width
  let start := ContinuousMap.startsAtZeroSet
  have hae : osc =ᵐ[μ] osc ∩ start := by
    filter_upwards [hstart] with path hpath
    simp [osc, start, ContinuousMap.startsAtZeroSet, hpath]
  have hmeasure : μ osc = μ (osc ∩ start) := measure_congr hae
  calc
    μ osc = μ (osc ∩ start) := hmeasure
    _ ≤ μ (⋃ j : Fin count,
          ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) := by
      apply measure_mono
      intro path hpath
      have hpath' : path 0 = 0 ∧
          ContinuousMap.rangeOscillationLe width path := by
        change path ∈ ContinuousMap.rangeOscillationSet width ∧
          path ∈ ContinuousMap.startsAtZeroSet at hpath
        have hosc : ∀ s t, |path s - path t| ≤ width := by
          intro s t
          exact Set.mem_iInter.mp
            (Set.mem_iInter.mp hpath.1 s) t
        exact ⟨hpath.2, hosc⟩
      exact ContinuousMap.rangeOscillationLe_subset_finiteCorridorCover
        width count hwidth hcount hpath'
    _ ≤ ∑ j : Fin count,
          μ (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) :=
      measure_iUnion_fintype_le μ _

end MeasureTheory.ContinuousMap

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackEntrance
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackIndexOne
public import Probability.Distributions.Stable.Support.IndexOne

/-!
# Entrance probability at stable index one

Nondegenerate strict 1-stability supplies mass on either side of every
target slope. Finite feedback blocks then produce the complete path and
endpoint event needed in the shifted-corridor comparison.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.measure_fullEntrance_pos_indexOne
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess 1 μ X P)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  let m : ℝ := min (1 + b) (min (1 - b)
    (min (1 + c) (min (1 - c) ε)))
  have hm : 0 < m := by
    dsimp [m]
    apply lt_min (by linarith)
    apply lt_min (by linarith)
    apply lt_min (by linarith)
    exact lt_min (by linarith) hε
  have hm_blo : m ≤ 1 + b := min_le_left _ _
  have hm_bhi : m ≤ 1 - b :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm_clo : m ≤ 1 + c :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hm_chi : m ≤ 1 - c :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
  have hm_eps : m ≤ ε := by
    dsimp [m]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  let η : ℝ := m / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have htube : 0 < P {ω | ∀ t : unitInterval,
      |X (unitIntervalToNNReal t) ω - (c - b) * (t : ℝ)| < η} :=
    h.linearTube_probability_pos_indexOne (c - b) η hη
      (h.increments.strictlyStable.measure_Ioi_pos_indexOne (c - b))
      (h.increments.strictlyStable.measure_Iio_pos_indexOne (c - b))
  let tube : Set Ω := {ω | ∀ t : unitInterval,
    |X (unitIntervalToNNReal t) ω - (c - b) * (t : ℝ)| < η}
  have hae : tube =ᵐ[P]
      tube ∩ fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε) := by
    filter_upwards [h.increments.ae_start_eq_zero] with ω hzero
    apply propext
    constructor
    · intro hω
      refine ⟨hω, ?_⟩
      exact linearTube_subset_fullEntrance X b c ε η hη
        (by dsimp [η]; linarith)
        (by dsimp [η]; linarith)
        (by dsimp [η]; linarith)
        (by dsimp [η]; linarith)
        (by dsimp [η]; linarith) ⟨hzero, hω⟩
    · exact And.left
  change 0 < P tube at htube
  rw [measure_congr hae] at htube
  exact htube.trans_le (measure_mono Set.inter_subset_right)

/-- The source endpoint convention has an open lower bound and a closed
upper bound. The positive open-window event is contained in it. -/
theorem IsStableLevyProcess.measure_sourceEntrance_pos_indexOne
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess 1 μ X P)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorEvent X 0 1 (c - 1) (c + 1) ∩
      {ω | c - b - ε < segmentIncrement X 0 1 ω ⊤ ∧
        segmentIncrement X 0 1 ω ⊤ ≤ c - b + ε}) := by
  have hp := h.measure_fullEntrance_pos_indexOne b c ε hb hc hε
  apply hp.trans_le
  apply measure_mono
  rintro ω ⟨hcorridor, hend⟩
  exact ⟨hcorridor, hend.1, hend.2.le⟩

end ProbabilityTheory

end

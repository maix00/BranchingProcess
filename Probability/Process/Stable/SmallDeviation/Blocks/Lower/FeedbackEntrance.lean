/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FeedbackTube
public import Probability.Distributions.Stable.Sign

/-!
# The unit-time entrance event in the interval comparison

The source's endpoint condition is left-open and right-closed. We prove
positivity through the smaller open endpoint window, keeping the source
corridor's strict global upper and lower bounds.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem linearTube_subset_fullEntrance
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    (b c ε η : ℝ) (hη : 0 < η)
    (hbLower : 2 * η < 1 + b) (hbUpper : 2 * η < 1 - b)
    (hcLower : 2 * η < 1 + c) (hcUpper : 2 * η < 1 - c)
    (hε : η < ε) :
    {ω | X 0 ω = 0 ∧ ∀ t : unitInterval,
      |X (unitIntervalToNNReal t) ω - (c - b) * (t : ℝ)| < η} ⊆
      fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε) := by
  rintro ω ⟨hzero, htube⟩
  have hline (t : unitInterval) :
      c - 1 + 2 * η ≤ (c - b) * (t : ℝ) ∧
        (c - b) * (t : ℝ) ≤ c + 1 - 2 * η := by
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    have hlo0 : 0 ≤ -(c - 1 + 2 * η) := by linarith
    have hlov : 0 ≤ (c - b) - (c - 1 + 2 * η) := by linarith
    have hhi0 : 0 ≤ c + 1 - 2 * η := by linarith
    have hhiv : 0 ≤ (c + 1 - 2 * η) - (c - b) := by linarith
    have hlo := mul_nonneg (sub_nonneg.mpr ht1) hlo0
    have hlov' := mul_nonneg ht0 hlov
    have hhi := mul_nonneg (sub_nonneg.mpr ht1) hhi0
    have hhiv' := mul_nonneg ht0 hhiv
    constructor <;> nlinarith
  have hcorridor : ω ∈ fullSegmentCorridorEvent X 0 1
      (c - 1) (c + 1) := by
    refine ⟨η, hη, ?_⟩
    intro t
    have hlt := abs_lt.mp (htube t)
    have hline' := hline t
    change c - 1 + η ≤
        X (0 + 1 * unitIntervalToNNReal t) ω - X 0 ω ∧
      X (0 + 1 * unitIntervalToNNReal t) ω - X 0 ω ≤ c + 1 - η
    simp only [zero_add, one_mul]
    rw [hzero]
    constructor <;> linarith
  have hend := abs_lt.mp (htube ⊤)
  have hendpoint : ω ∈ {ω | segmentIncrement X 0 1 ω ⊤ ∈
      Set.Ioo (c - b - ε) (c - b + ε)} := by
    change c - b - ε < X (0 + 1 * unitIntervalToNNReal ⊤) ω - X 0 ω ∧
      X (0 + 1 * unitIntervalToNNReal ⊤) ω - X 0 ω < c - b + ε
    simp only [zero_add, one_mul, unitIntervalToNNReal_top]
    rw [hzero]
    simp only [sub_zero]
    have htop : ((⊤ : unitInterval) : ℝ) = 1 := rfl
    rw [htop] at hend
    rw [unitIntervalToNNReal_top] at hend
    constructor <;> linarith
  exact ⟨hcorridor, hendpoint⟩

/-- The complete-path feedback tube supplies the exact positive entrance
factor needed in the interval comparison, with an open endpoint window. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_of_linearTube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hα : 1 < α) (hpos : 0 < μ (Set.Ioi 0))
    (hneg : 0 < μ (Set.Iio 0))
    (b c ε η : ℝ) (hη : 0 < η)
    (hbLower : 2 * η < 1 + b) (hbUpper : 2 * η < 1 - b)
    (hcLower : 2 * η < 1 + c) (hcUpper : 2 * η < 1 - c)
    (hε : η < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  let tube : Set Ω := {ω | ∀ t : unitInterval,
    |X (unitIntervalToNNReal t) ω - (c - b) * (t : ℝ)| < η}
  have htube : 0 < P tube :=
    h.linearTube_probability_pos hα hpos hneg (c - b) η hη
  have hae : tube =ᵐ[P]
      tube ∩ fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε) := by
    filter_upwards [h.increments.ae_start_eq_zero] with ω hzero
    apply propext
    constructor
    · intro hω
      refine ⟨hω, ?_⟩
      exact linearTube_subset_fullEntrance X b c ε η hη
        hbLower hbUpper hcLower hcUpper hε ⟨hzero, hω⟩
    · exact And.left
  rw [measure_congr hae] at htube
  exact htube.trans_le (measure_mono Set.inter_subset_right)

/-- Under the paper's `|b|,|c|<1` conditions, the stable-process entrance
factor is positive for every positive endpoint tolerance when `α>1`. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hα : 1 < α) (hpos : 0 < μ (Set.Ioi 0))
    (hneg : 0 < μ (Set.Iio 0))
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
  exact h.measure_fullEntrance_pos_of_linearTube hα hpos hneg
    b c ε (m / 4) (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith)

/-- The source CDF hypothesis supplies the two sign masses used by the
feedback construction. No path-space support or atomlessness is assumed. -/
theorem IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 1 < α)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  exact h.measure_fullEntrance_pos hα hpos hneg b c ε hb hc hε

/-- Positivity for the source's left-open, right-closed endpoint convention.
The open endpoint event proved above is a measurable subset of this one. -/
theorem IsStableLevyProcess.measure_sourceEntrance_pos_of_cdfAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (hα : 1 < α)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hε : 0 < ε) :
    0 < P (fullSegmentCorridorEvent X 0 1 (c - 1) (c + 1) ∩
      {ω | c - b - ε < segmentIncrement X 0 1 ω ⊤ ∧
        segmentIncrement X 0 1 ω ⊤ ≤ c - b + ε}) := by
  have hp := h.measure_fullEntrance_pos_of_cdfAtZero hα hcdf
    b c ε hb hc hε
  apply hp.trans_le
  apply measure_mono
  rintro ω ⟨hcorridor, hend⟩
  exact ⟨hcorridor, hend.1, hend.2.le⟩

end ProbabilityTheory

end

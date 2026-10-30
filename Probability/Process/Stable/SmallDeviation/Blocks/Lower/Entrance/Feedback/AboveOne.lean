/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.CDF
public import Probability.Process.Corridor.Segment
public import Probability.Process.Stable.Levy
import Probability.Distributions.Stable.Support.Sign
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Feedback.Tube

/-!
# Positive entrance for stable index greater than one

## Public declarations

- IsStableLevyProcess.measure_fullEntrance_pos: under \(\alpha>1\),
  \(b,c\in(-1,1)\), \(\varepsilon>0\), and positive mass on both sign
  half-lines, the same entrance event has positive probability.
- IsStableLevyProcess.measure_fullEntrance_pos_of_cdfAtZero: the preceding
  conclusion follows from \(0<F_\mu(0)<1\).
- IsStableLevyProcess.measure_sourceEntrance_pos_of_cdfAtZero: under the same
  CDF condition, the complete corridor event jointly with
  \(c-b-\varepsilon<X_1-X_0\le c-b+\varepsilon\) has positive probability.

The return event uses a left-open and right-closed endpoint interval. We
prove positivity through a smaller open endpoint window, keeping the strict
global corridor bounds.

This entrance estimate supplies the positive endpoint-window factor used in
Lemma 2(a), equation (21), of A. A. Mogul'skii, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The complete-path feedback tube supplies the exact positive entrance
factor needed in the interval comparison, with an open endpoint window. -/
private lemma IsStableLevyProcess.measure_fullEntrance_pos_of_linearTube
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
    |X (unitInterval.toNNReal t) ω - (c - b) * (t : ℝ)| < η}
  have htube : 0 < P tube :=
    h.linearTube_probability_pos hα hpos hneg (c - b) η hη
  have hgeometry :
      {ω | ∀ t : unitInterval,
        |segmentIncrement X 0 1 ω t - (c - b) * (t : ℝ)| < η} ⊆
        fullSegmentCorridorReturnEvent X 0 1
          (c - 1) (c + 1) (c - b - ε) (c - b + ε) :=
    linearTube_subset_fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε) (c - b) η hη
      (by constructor <;> linarith)
      (by constructor <;> linarith)
      (by constructor <;> linarith)
  have hae : tube =ᵐ[P]
      tube ∩ fullSegmentCorridorReturnEvent X 0 1
        (c - 1) (c + 1) (c - b - ε) (c - b + ε) := by
    filter_upwards [h.increments.ae_start_eq_zero] with ω hzero
    apply propext
    constructor
    · intro hω
      refine ⟨hω, ?_⟩
      apply hgeometry
      intro t
      have hzero' : X 0 ω = 0 := by simpa using hzero
      change |X (0 + 1 * unitInterval.toNNReal t) ω - X 0 ω -
        (c - b) * (t : ℝ)| < η
      simp only [zero_add, one_mul]
      rw [hzero']
      simpa only [sub_zero] using hω t
    · exact And.left
  rw [measure_congr hae] at htube
  exact htube.trans_le (measure_mono Set.inter_subset_right)

/-- When `|b|, |c| < 1`, the stable-process entrance factor is positive for
every positive endpoint tolerance when `α > 1`. -/
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

/-- The strict CDF inequalities at zero supply positive increment mass on
both half-lines, as required by the feedback construction. -/
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

/-- Positivity for the endpoint condition
`c - b - ε < X(1) - X(0) ≤ c - b + ε`. The open endpoint event proved above
is a measurable subset of this one. -/
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

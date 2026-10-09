/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing

/-!
# From strict rational bounds to complete-path corridors

Pointwise strict rational bounds do not themselves imply a uniform margin.
Enlarging the spatial corridor supplies that margin before the càdlàg
dense-coordinate theorem is applied.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem measure_rationalCorridorReturn_le_fullSegmentCorridorReturn_enlarged
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (length : ℝ≥0)
    (lower upper coreLower coreUpper extra : ℝ) (hextra : 0 < extra)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    P ((fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) ≤
      P (fullSegmentCorridorReturnEvent X 0 length
        (lower - extra) (upper + extra) coreLower coreUpper) := by
  apply measure_mono_ae
  filter_upwards [hcadlag] with ω hω
  intro hstrict
  apply (mem_fullSegmentCorridorReturnEvent_iff_rational X 0 length
    (lower - extra) (upper + extra) coreLower coreUpper ω hω).2
  have hmargin := rationalCoordinateCorridorReturn_subset_withMargin_enlarged
    lower upper coreLower coreUpper extra hextra hstrict
  simpa only [zero_add] using hmargin

/-- An oscillation tube of sufficiently small width forces the complete
centered path into any corridor containing the origin. -/
theorem measure_rationalHorizonTube_le_fullSegmentCorridor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (length : ℝ≥0)
    (lower upper width : ℝ) (_hwidth : 0 < width)
    (hlower : lower < -width) (hupper : width < upper)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)) :
    P (rationalHorizonTubeEvent X length width) ≤
      P (fullSegmentCorridorEvent X 0 length lower upper) := by
  let clearance : ℝ := min (-width - lower) (upper - width)
  have hclearance : 0 < clearance := by
    dsimp [clearance]
    exact lt_min (by linarith) (by linarith)
  obtain ⟨margin, hmargin, hmarginClear⟩ := exists_rat_btwn hclearance
  apply measure_mono_ae
  filter_upwards [hcadlag] with ω hω
  intro htube
  apply (mem_fullSegmentCorridorEvent_iff_rational
    X 0 length lower upper ω hω).2
  refine ⟨margin, hmargin, ?_⟩
  intro q
  obtain ⟨tubeMargin, htubeMargin, hbound⟩ := htube
  have hq := hbound q ⊥
  have hbot : length * RationalCoordinate.toNNReal ⊥ = 0 := by simp [RationalCoordinate.toNNReal_bot]
  change |X (length * RationalCoordinate.toNNReal q) ω -
    X (length * RationalCoordinate.toNNReal ⊥) ω| ≤ width - tubeMargin at hq
  rw [hbot] at hq
  have hq' := abs_le.mp hq
  have hmarginLower : (margin : ℝ) < -width - lower :=
    lt_of_lt_of_le hmarginClear (min_le_left _ _)
  have hmarginUpper : (margin : ℝ) < upper - width :=
    lt_of_lt_of_le hmarginClear (min_le_right _ _)
  constructor <;> simp only [zero_add] <;> linarith

end ProbabilityTheory

end

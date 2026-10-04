/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.Upper.Scale
public import MeasureTheory.Measure.PositiveTail

/-!
# Strict loss of tube probability

A positive upper tail for the reference increment law prevents the unit-time
range tube from having probability one. Together with the scaled block upper
bound, this yields an exponential upper estimate.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem rationalHorizonTubeEvent_disjoint_largePositiveIncrement
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (width : ℝ) :
    Disjoint (rationalHorizonTubeEvent X 1 width)
      {ω | width < X 1 ω - X 0 ω} := by
  apply Set.disjoint_left.mpr
  intro ω hω hlarge
  obtain ⟨margin, hmargin, hbound⟩ := hω
  have hendpoint := hbound ⊤ ⊥
  simp only [rationalHorizonProcess, one_mul, rationalUnitTime_top,
    rationalUnitTime_bot] at hendpoint
  change |X 1 ω - X 0 ω| ≤ width - (margin : ℝ) at hendpoint
  change width < X 1 ω - X 0 ω at hlarge
  have habs := le_abs_self (X 1 ω - X 0 ω)
  linarith

/-- If the reference law gives positive mass to an increment beyond the
tube width, the unit-time tube has probability strictly less than one. -/
theorem IsStableLevyProcess.measure_rationalHorizonTube_lt_one_of_positive_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (width : ℝ) (htail : 0 < μ (Set.Ioi width)) :
    P (rationalHorizonTubeEvent X 1 width) < 1 := by
  let F : Set Ω := {ω | width < X 1 ω - X 0 ω}
  have hlaw := h.increments.increment_hasLaw 0 1 (by exact bot_le)
  have hF : P F = μ (Set.Ioi width) := by
    have heq := hlaw.measure_eq (p := fun x : ℝ => width < x) measurableSet_Ioi
    simpa [F, Set.Ioi] using heq
  have hFmeas : NullMeasurableSet F P := by
    exact (hlaw.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi)
  have hcompl : P Fᶜ < 1 := by
    have hsum := measure_add_measure_compl₀ hFmeas
    rw [measure_univ] at hsum
    have hpositive : 0 < P F := hF ▸ htail
    have hlt := ENNReal.lt_add_right (measure_lt_top P Fᶜ).ne hpositive.ne'
    rw [add_comm, hsum] at hlt
    exact hlt
  exact (measure_mono
    (Set.subset_compl_iff_disjoint_right.mpr
      (rationalHorizonTubeEvent_disjoint_largePositiveIncrement X width))).trans_lt
    hcompl

/-- Every partition length has a strict exponential upper estimate at the
corresponding stable width, with the base given by one fixed unit-time tube
probability. -/
theorem IsStableLevyProcess.measure_scaledTube_le_pow_strict
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (width : ℝ) (htail : 0 < μ (Set.Ioi width))
    (blocks : ℕ) (hblocks : 0 < blocks) :
    let scale : ℝ :=
      ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
    P (rationalHorizonTubeEvent X 1 (width / scale)) ≤
      P (rationalHorizonTubeEvent X 1 width) ^ blocks ∧
    P (rationalHorizonTubeEvent X 1 width) < 1 := by
  let scale : ℝ :=
    ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^ (-(1 / α))
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hscale : scale ≠ 0 := ne_of_gt
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr ht) _)
  have hupper := h.measure_rationalTube_le_pow_scaledBlock
    blocks hblocks (width / scale)
  dsimp only at hupper
  have hcancel : width / scale * scale = width :=
    div_mul_cancel₀ width hscale
  dsimp only [scale] at hcancel
  rw [hcancel] at hupper
  exact ⟨hupper, h.measure_rationalHorizonTube_lt_one_of_positive_tail
    width htail⟩

/-- Positive mass on one side of the stable reference law yields a fixed
strictly subunit base for exponential upper bounds along all stable
shrinking-width partitions. -/
theorem IsStableLevyProcess.exists_strict_exponential_tube_upper_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (hpos : 0 < μ (Set.Ioi 0)) :
    ∃ width : ℝ, ∃ c : ENNReal, 0 < width ∧ c < 1 ∧
      ∀ blocks : ℕ, ∀ hblocks : 0 < blocks,
        P (rationalHorizonTubeEvent X 1
          (width /
            (((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
              (-(1 / α))))) ≤ c ^ blocks := by
  obtain ⟨width, hwidth, htail⟩ := MeasureTheory.exists_positive_tail_threshold μ hpos
  let c : ENNReal := P (rationalHorizonTubeEvent X 1 width)
  refine ⟨width, c, hwidth,
    h.measure_rationalHorizonTube_lt_one_of_positive_tail width htail, ?_⟩
  intro blocks hblocks
  exact (h.measure_scaledTube_le_pow_strict width htail blocks hblocks).1

end ProbabilityTheory

end

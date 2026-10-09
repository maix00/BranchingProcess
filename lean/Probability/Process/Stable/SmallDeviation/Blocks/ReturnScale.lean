/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.RationalTube
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks

/-!
# Stable scaling for returning corridor blocks

The centered path law follows from the finite-dimensional stable-process law.
It gives the exact time-space scaling of a corridor with an endpoint return
window, the local probability appearing in block lower bounds.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Centering the rational restriction of a stable process commutes with
stable scaling in distribution. -/
theorem IsStableLevyProcess.centeredRationalRestriction_identDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon) :
    IdentDistrib
      (fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω)
      (fun ω q => (horizon : ℝ) ^ (-(1 / α)) *
        (X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)) P P := by
  have hlaw := (h.rationalRestriction_identDistrib horizon hhorizon).comp
    measurable_centerRationalPath
  convert hlaw using 1
  · funext ω q
    simp [centerRationalPath, rationalHorizonProcess, RationalCoordinate.toNNReal_bot]
  · funext ω q
    simp [centerRationalPath, rationalHorizonProcess, RationalCoordinate.toNNReal_bot]
    ring

/-- Stable scaling carries both the path corridor and the endpoint return
window. The right-hand event is expressed through the original process at
the requested horizon. -/
theorem IsStableLevyProcess.corridorReturn_timeSpaceScale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) =
    P ((fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (lower / ((horizon : ℝ) ^ (-(1 / α))))
        (upper / ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower / ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper / ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hlaw := h.centeredRationalRestriction_identDistrib horizon hhorizon
  have hprob := hlaw.measure_mem_eq
    (measurableSet_rationalCoordinateCorridorReturn lower upper coreLower coreUpper)
  have hevent :
      (fun ω q => scale *
          (X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
          rationalCoordinateCorridorReturn lower upper coreLower coreUpper =
        (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
          rationalCoordinateCorridorReturn
            (lower / scale) (upper / scale)
            (coreLower / scale) (coreUpper / scale) := by
    ext ω
    exact mem_rationalCoordinateCorridorReturn_smul_iff scale hscale
      (fun q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)
      lower upper coreLower coreUpper
  rw [hevent] at hprob
  simpa [scale] using hprob

/-- The first block of an `(n+1)`-fold uniform partition is exactly the
short-horizon path in the stable corridor-return scaling identity. -/
theorem IsStableLevyProcess.firstBlock_corridorReturn_scale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (n : ℕ)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) =
    P ((fun ω q => rationalUniformBlockProcessFromTime X
        (Nat.succ_pos n) ⟨0, Nat.succ_pos n⟩ q ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (lower / (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (-(1 / α))))
        (upper / (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (-(1 / α))))
        (coreLower / (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (-(1 / α))))
        (coreUpper / (((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) ^ (-(1 / α))))) := by
  have htime : (0 : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) := by positivity
  have hscale := h.corridorReturn_timeSpaceScale
    (1 / ((n : ℝ≥0) + 1)) htime lower upper coreLower coreUpper
  rw [rationalUniformBlockProcess_zero_eq_initial,
    rationalUniformBlockBoundary_succ_one] at *
  exact hscale

/-- The reverse orientation is convenient when a block estimate already
specifies the short-time corridor and return window. -/
theorem IsStableLevyProcess.corridorReturn_timeSpaceScale_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) =
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hs : scale ≠ 0 := ne_of_gt
    (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _)
  have hscale := h.corridorReturn_timeSpaceScale horizon hhorizon
    (lower * scale) (upper * scale) (coreLower * scale) (coreUpper * scale)
  dsimp only [scale] at hscale hs
  simp only [mul_div_cancel_right₀ _ hs] at hscale
  exact hscale.symm

/-- A first uniform block can be evaluated as a unit-time stable path in
the appropriately scaled corridor and return window. -/
theorem IsStableLevyProcess.firstBlock_corridorReturn_scale_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) =
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (lower * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (upper * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (coreLower * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))
        (coreUpper * ((rationalUniformBlockBoundary blocks 1 hblocks : ℝ≥0) : ℝ) ^
          (-(1 / α)))) := by
  have ht : 0 < rationalUniformBlockBoundary blocks 1 hblocks := by
    apply NNReal.coe_pos.mp
    simp only [rationalUniformBlockBoundary, Nat.cast_one]
    have hb : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
    change 0 < (1 : ℝ) / (blocks : ℝ)
    positivity
  have hscale := h.corridorReturn_timeSpaceScale_inv
    (rationalUniformBlockBoundary blocks 1 hblocks) ht
    lower upper coreLower coreUpper
  rw [rationalUniformBlockProcess_zero_eq_initial]
  exact hscale

end ProbabilityTheory

end

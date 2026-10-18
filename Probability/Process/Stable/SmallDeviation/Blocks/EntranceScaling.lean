/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Levy
public import Probability.Process.Path.Skorokhod.RationalTime
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
import Probability.Process.Stable.SmallDeviation.Blocks.ReturnScale

/-!
# The stable short entrance block

At duration `a ^ α`, a corridor and endpoint window scaled by `a` have the
same probability as the unscaled unit-time event. This is the scaling step
in the entrance factor of the shifted-corridor comparison.

The public declarations are:

* `stableEntranceHorizon α a = Real.toNNReal (a ^ α)`, the time associated
  with spatial scale `a` for a stable process of index `α`.
* `IsStableLevyProcess.corridorReturnWithMargin_timeSpaceScale_inv`: the
  rational-time positive-margin return-corridor probability at horizon `T`
  equals the unit-time probability after multiplying all spatial bounds by
  `T ^ (-1 / α)`.
* `IsStableLevyProcess.measure_fullSegmentCorridorReturn_scale`: the same
  scaling identity for the complete càdlàg segment event.
* `IsStableLevyProcess.shortEntrance_corridorReturn_probability` and
  `IsStableLevyProcess.shortEntrance_fullCorridorReturn_probability`: at
  `T = a ^ α`, scaling every corridor and return bound by `a` leaves the
  rational-time and complete-path probabilities unchanged.
* `IsStableLevyProcess.corridorIocReturn_timeSpaceScale` and
  `IsStableLevyProcess.measure_fullSegmentCorridorIocReturn_scale`: the
  corresponding identities for a left-open, right-closed endpoint window.
* `IsStableLevyProcess.shortEntrance_fullSegmentCorridorIocReturn_probability`:
  the complete-path left-open, right-closed version at time `a ^ α`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The short entrance time corresponding to spatial scale `a`. -/
noncomputable def stableEntranceHorizon (α a : ℝ) : ℝ≥0 :=
  Real.toNNReal (a ^ α)

/-- The positive-margin version of stable corridor scaling. This is the
countable-coordinate calculation used to prove the full-path statement. -/
theorem IsStableLevyProcess.corridorReturnWithMargin_timeSpaceScale_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper) =
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hlaw := h.centeredRationalRestriction_identDistrib horizon hhorizon
  have hprob := hlaw.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
      (lower * scale) (upper * scale) (coreLower * scale) (coreUpper * scale))
  have hevent :
      (fun ω q => scale *
          (X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
          Skorokhod.rationalCoordinateCorridorReturnWithMargin
            (lower * scale) (upper * scale)
            (coreLower * scale) (coreUpper * scale) =
        (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorReturnWithMargin
            lower upper coreLower coreUpper := by
    ext ω
    have hs := Skorokhod.mem_rationalCoordinateCorridorReturnWithMargin_smul_iff
      scale hscale
      (fun q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)
      (lower * scale) (upper * scale)
      (coreLower * scale) (coreUpper * scale)
    simpa only [Set.mem_preimage, mul_div_cancel_right₀ _ hscale.ne'] using hs
  rw [hevent] at hprob
  simpa [scale] using hprob.symm

/-- Stable scaling of the endpoint-constrained corridor as a complete-path
event. The countable coordinates are confined to the proof. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridorReturn_scale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 horizon
        lower upper coreLower coreUpper) =
      P (fullSegmentCorridorReturnEvent X 0 1
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α))))) := by
  have hs := h.corridorReturnWithMargin_timeSpaceScale_inv horizon hhorizon
    lower upper coreLower coreUpper
  have haeShort :
      (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        Skorokhod.rationalCoordinateCorridorReturnWithMargin
          lower upper coreLower coreUpper =ᵐ[P]
      fullSegmentCorridorReturnEvent X 0 horizon
        lower upper coreLower coreUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [zero_add] using propext
      (mem_fullSegmentCorridorReturnEvent_iff_rational
        X 0 horizon lower upper coreLower coreUpper ω hω).symm
  have haeUnit :
      (fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
        Skorokhod.rationalCoordinateCorridorReturnWithMargin
          (lower * ((horizon : ℝ) ^ (-(1 / α))))
          (upper * ((horizon : ℝ) ^ (-(1 / α))))
          (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
          (coreUpper * ((horizon : ℝ) ^ (-(1 / α)))) =ᵐ[P]
      fullSegmentCorridorReturnEvent X 0 1
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α)))) := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [zero_add, one_mul] using propext
      (mem_fullSegmentCorridorReturnEvent_iff_rational X 0 1
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α)))) ω hω).symm
  rw [measure_congr haeShort, measure_congr haeUnit] at hs
  exact hs

/-- At time `a ^ α`, scaling the spatial corridor and return bounds by `a`
preserves the probability of the rational-coordinate return event. -/
theorem IsStableLevyProcess.shortEntrance_corridorReturn_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X ((stableEntranceHorizon α a) *
        RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn
        (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) =
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      rationalCoordinateCorridorReturn lower upper coreLower coreUpper) := by
  let horizon : ℝ≥0 := stableEntranceHorizon α a
  have hhorizon : 0 < horizon := by
    apply NNReal.coe_pos.mp
    simp [horizon, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hα : 0 < α := h.increments.strictlyStable.1
  have hscale : (horizon : ℝ) ^ (-(1 / α)) = a⁻¹ := by
    rw [show (horizon : ℝ) = a ^ α by
      simp [horizon, stableEntranceHorizon,
        Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by
      field_simp
    rw [hexp, Real.rpow_neg_one]
  have hs := h.corridorReturn_timeSpaceScale_inv horizon hhorizon
    (a * lower) (a * upper) (a * coreLower) (a * coreUpper)
  simp only [hscale] at hs
  have ha0 : a ≠ 0 := ha.ne'
  have hcancel (x : ℝ) : a * x * a⁻¹ = x := by
    field_simp
  rw [hcancel lower, hcancel upper, hcancel coreLower, hcancel coreUpper] at hs
  simpa [horizon] using hs

/-- At time `a ^ α`, the complete-path entrance probability is exactly its
unit-time unscaled counterpart. -/
theorem IsStableLevyProcess.shortEntrance_fullCorridorReturn_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 (stableEntranceHorizon α a)
        (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) =
      P (fullSegmentCorridorReturnEvent X 0 1
        lower upper coreLower coreUpper) := by
  let horizon : ℝ≥0 := stableEntranceHorizon α a
  have hhorizon : 0 < horizon := by
    apply NNReal.coe_pos.mp
    simp [horizon, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hα : 0 < α := h.increments.strictlyStable.1
  have hscale : (horizon : ℝ) ^ (-(1 / α)) = a⁻¹ := by
    rw [show (horizon : ℝ) = a ^ α by
      simp [horizon, stableEntranceHorizon,
        Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by field_simp
    rw [hexp, Real.rpow_neg_one]
  have hs := h.measure_fullSegmentCorridorReturn_scale horizon hhorizon
    (a * lower) (a * upper) (a * coreLower) (a * coreUpper)
  simp only [hscale] at hs
  have hcancel (x : ℝ) : a * x * a⁻¹ = x := by field_simp
  rw [hcancel lower, hcancel upper, hcancel coreLower, hcancel coreUpper] at hs
  simpa [horizon] using hs

/-- The rational-coordinate probability of the complete corridor with an
`Ioc` endpoint window obeys stable time-space scaling. -/
theorem IsStableLevyProcess.corridorIocReturn_timeSpaceScale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P ((fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        lower upper coreLower coreUpper) =
    P ((fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
        (lower / ((horizon : ℝ) ^ (-(1 / α))))
        (upper / ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower / ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper / ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hlaw := h.centeredRationalRestriction_identDistrib horizon hhorizon
  have hprob := hlaw.measure_mem_eq
    (Skorokhod.measurableSet_rationalCoordinateCorridorIocReturnWithMargin
      lower upper coreLower coreUpper)
  have hevent :
      (fun ω q => scale *
          (X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lower upper coreLower coreUpper =
        (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (lower / scale) (upper / scale)
            (coreLower / scale) (coreUpper / scale) := by
    ext ω
    exact Skorokhod.mem_rationalCoordinateCorridorIocReturnWithMargin_smul_iff
      scale hscale
      (fun q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω)
      lower upper coreLower coreUpper
  rw [hevent] at hprob
  simpa [scale] using hprob

/-- Stable scaling for the complete-path corridor with a left-open,
right-closed endpoint window. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridorIocReturn_scale
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (horizon : ℝ≥0) (hhorizon : 0 < horizon)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorIocReturnEvent X 0 horizon
        lower upper coreLower coreUpper) =
      P (fullSegmentCorridorIocReturnEvent X 0 1
        (lower * ((horizon : ℝ) ^ (-(1 / α))))
        (upper * ((horizon : ℝ) ^ (-(1 / α))))
        (coreLower * ((horizon : ℝ) ^ (-(1 / α))))
        (coreUpper * ((horizon : ℝ) ^ (-(1 / α))))) := by
  let scale : ℝ := (horizon : ℝ) ^ (-(1 / α))
  have hscale : 0 < scale :=
    Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hhorizon) _
  have hs := h.corridorIocReturn_timeSpaceScale horizon hhorizon
    (lower * scale) (upper * scale) (coreLower * scale) (coreUpper * scale)
  have hcancel (x : ℝ) : x * scale / scale = x := mul_div_cancel_right₀ x hscale.ne'
  rw [hcancel lower, hcancel upper, hcancel coreLower, hcancel coreUpper] at hs
  have haeHorizon :
      (fun ω q => X (horizon * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            lower upper coreLower coreUpper =ᵐ[P]
        fullSegmentCorridorIocReturnEvent X 0 horizon
          lower upper coreLower coreUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [zero_add, one_mul] using propext
      (mem_fullSegmentCorridorIocReturnEvent_iff_rational
        X 0 horizon lower upper coreLower coreUpper ω hω).symm
  have haeUnit :
      (fun ω q => X (RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
          Skorokhod.rationalCoordinateCorridorIocReturnWithMargin
            (lower * scale) (upper * scale)
            (coreLower * scale) (coreUpper * scale) =ᵐ[P]
        fullSegmentCorridorIocReturnEvent X 0 1
          (lower * scale) (upper * scale)
          (coreLower * scale) (coreUpper * scale) := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [zero_add, one_mul] using propext
      (mem_fullSegmentCorridorIocReturnEvent_iff_rational
        X 0 1 (lower * scale) (upper * scale)
        (coreLower * scale) (coreUpper * scale) ω hω).symm
  rw [measure_congr haeHorizon, measure_congr haeUnit] at hs
  simpa [scale] using hs.symm

/-- At time `a ^ α`, the complete-path corridor probability with the
source's left-open, right-closed endpoint convention equals its unit-time
unscaled value. -/
theorem IsStableLevyProcess.shortEntrance_fullSegmentCorridorIocReturn_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (a : ℝ) (ha : 0 < a)
    (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorIocReturnEvent X 0 (stableEntranceHorizon α a)
        (a * lower) (a * upper) (a * coreLower) (a * coreUpper)) =
      P (fullSegmentCorridorIocReturnEvent X 0 1
        lower upper coreLower coreUpper) := by
  let horizon : ℝ≥0 := stableEntranceHorizon α a
  have hhorizon : 0 < horizon := by
    apply NNReal.coe_pos.mp
    simp [horizon, stableEntranceHorizon,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]
    exact Real.rpow_pos_of_pos ha α
  have hα : 0 < α := h.increments.strictlyStable.1
  have hscale : (horizon : ℝ) ^ (-(1 / α)) = a⁻¹ := by
    rw [show (horizon : ℝ) = a ^ α by
      simp [horizon, stableEntranceHorizon,
        Real.coe_toNNReal _ (Real.rpow_pos_of_pos ha α).le]]
    rw [← Real.rpow_mul ha.le]
    have hexp : α * (-(1 / α)) = -1 := by field_simp
    rw [hexp, Real.rpow_neg_one]
  have hs := h.measure_fullSegmentCorridorIocReturn_scale horizon hhorizon
    (a * lower) (a * upper) (a * coreLower) (a * coreUpper)
  simp only [hscale] at hs
  have hcancel (x : ℝ) : a * x * a⁻¹ = x := by field_simp
  rw [hcancel lower, hcancel upper, hcancel coreLower, hcancel coreUpper] at hs
  simpa [horizon] using hs

end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.Shift
public import Probability.Process.Path.Skorokhod.Corridor.Segment

/-!
# Stationarity of complete-path corridor probabilities

The process shifted by a deterministic time has the same stable increment
specification. Equality of complete-segment corridor probabilities follows
from finite-dimensional uniqueness and càdlàg path regularity.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.centeredSegment_identDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (start length : ℝ≥0) :
    IdentDistrib
      (fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω)
      (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω)
      P P := by
  let clock : RationalCoordinate.UnitInterval → ℝ≥0 :=
    fun q => length * RationalCoordinate.toNNReal q
  have hclockMono : Monotone clock := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (RationalCoordinate.monotone_toNNReal hst) length.property
  have hclockBot : clock ⊥ = 0 := by
    simp [clock, RationalCoordinate.toNNReal_bot]
  have hbase := h.increments.comp_time clock hclockMono hclockBot
  have hshift := (h.shifted start).increments.comp_time
    clock hclockMono hclockBot
  have hlaw := (hbase.process_identDistrib hshift).comp
    measurable_centerRationalPath
  convert hlaw using 1
  · funext ω q
    simp [centerRationalPath, clock, RationalCoordinate.toNNReal_bot]
  · funext ω q
    simp [centerRationalPath, clock, RationalCoordinate.toNNReal_bot]

theorem IsStableLevyProcess.measure_fullSegmentCorridor_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (start length : ℝ≥0) (lower upper : ℝ) :
    P (fullSegmentCorridorEvent X 0 length lower upper) =
      P (fullSegmentCorridorEvent X start length lower upper) := by
  let A : Set Ω :=
    (fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  let B : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  have hlaw : P A = P B := by
    exact (h.centeredSegment_identDistrib start length).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin lower upper)
  have haeA : A =ᵐ[P] fullSegmentCorridorEvent X 0 length lower upper := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [A, zero_add] using propext
      (mem_fullSegmentCorridorEvent_iff_rational
        X 0 length lower upper ω hω).symm
  have haeB : B =ᵐ[P]
      fullSegmentCorridorEvent X start length lower upper := by
    filter_upwards [h.ae_cadlag] with ω hω
    exact propext (mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).symm
  rw [measure_congr haeA, measure_congr haeB] at hlaw
  exact hlaw

/-- Endpoint-constrained complete corridor probabilities are invariant under
deterministic time shifts. -/
theorem IsStableLevyProcess.measure_fullSegmentCorridorReturn_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (start length : ℝ≥0) (lower upper coreLower coreUpper : ℝ) :
    P (fullSegmentCorridorReturnEvent X 0 length
      lower upper coreLower coreUpper) =
      P (fullSegmentCorridorReturnEvent X start length
        lower upper coreLower coreUpper) := by
  let A : Set Ω :=
    (fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  let B : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω - X start ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  have hlaw : P A = P B := by
    exact (h.centeredSegment_identDistrib start length).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper)
  have haeA : A =ᵐ[P] fullSegmentCorridorReturnEvent X 0 length
      lower upper coreLower coreUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    simpa [A, zero_add] using propext
      (mem_fullSegmentCorridorReturnEvent_iff_rational
        X 0 length lower upper coreLower coreUpper ω hω).symm
  have haeB : B =ᵐ[P] fullSegmentCorridorReturnEvent X start length
      lower upper coreLower coreUpper := by
    filter_upwards [h.ae_cadlag] with ω hω
    exact propext (mem_fullSegmentCorridorReturnEvent_iff_rational
      X start length lower upper coreLower coreUpper ω hω).symm
  rw [measure_congr haeA, measure_congr haeB] at hlaw
  exact hlaw

end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.StationaryIncrements.Basic
import Probability.Process.IndepIncrements.PathLaw.StationaryTimeChange

/-!
# Translation invariance of complete-segment corridor events

For a real-valued process with independent stationary increments and
almost-surely càdlàg paths, complete-segment corridor probabilities are
invariant under deterministic time translation. The process need not start at
zero, and no stable-law or scaling assumption is used.

The public results are `HasIndepIncrements.measure_fullSegmentCorridor_shift`
and `HasIndepIncrements.measure_fullSegmentCorridorReturn_shift`. The first
states
\[
  \mathbb P\bigl(X_t-X_0\in C\text{ for }0\le t\le T\bigr)
  =
  \mathbb P\bigl(X_{s+t}-X_s\in C\text{ for }0\le t\le T\bigr),
\]
and the second includes a prescribed terminal return window. Their proofs use
the general path-law theorem for equal-duration time changes and the rational
coordinate characterization of càdlàg corridor events.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

private theorem centeredRationalSegment_identDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hindep : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (start length : ℝ≥0) :
    IdentDistrib
      (fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω)
      (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω -
        X start ω) P P := by
  let τ₀ : RationalCoordinate.UnitInterval → ℝ≥0 :=
    fun q => length * RationalCoordinate.toNNReal q
  let τ₁ : RationalCoordinate.UnitInterval → ℝ≥0 :=
    fun q => start + length * RationalCoordinate.toNNReal q
  have hτ₀mono : Monotone τ₀ := by
    intro q r hqr
    exact mul_le_mul_of_nonneg_left
      (RationalCoordinate.monotone_toNNReal hqr) length.property
  have hτ₁mono : Monotone τ₁ := by
    intro q r hqr
    simpa [τ₁] using add_le_add_right
      (mul_le_mul_of_nonneg_left
        (RationalCoordinate.monotone_toNNReal hqr) length.property) start
  have hduration (q r : RationalCoordinate.UnitInterval) (hqr : q ≤ r) :
      τ₀ r - τ₀ q = τ₁ r - τ₁ q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (hτ₀mono hqr), NNReal.coe_sub (hτ₁mono hqr)]
    simp [τ₀, τ₁]
  have hpath₀ : AEMeasurable
      (fun ω q => X (τ₀ q) ω - X (τ₀ ⊥) ω) P := by
    exact AEMeasurable.of_eval fun q => by
      let d := τ₀ q - τ₀ ⊥
      have hsum : τ₀ ⊥ + d = τ₀ q :=
        add_tsub_cancel_of_le (hτ₀mono bot_le)
      have hq := hstationary (τ₀ ⊥) d
      simpa [τ₀, d, hsum] using hq.aemeasurable_fst
  have hpath₁ : AEMeasurable
      (fun ω q => X (τ₁ q) ω - X (τ₁ ⊥) ω) P := by
    exact AEMeasurable.of_eval fun q => by
      let d := τ₁ q - τ₁ ⊥
      have hsum : τ₁ ⊥ + d = τ₁ q :=
        add_tsub_cancel_of_le (hτ₁mono bot_le)
      have hq := hstationary (τ₁ ⊥) d
      simpa [τ₁, d, hsum] using hq.aemeasurable_fst
  have hlaw := hindep.process_identDistrib_of_sameDuration_timeChanges
    hstationary τ₀ τ₁ hτ₀mono hτ₁mono hduration hpath₀ hpath₁
  simpa [τ₀, τ₁, RationalCoordinate.toNNReal_bot] using hlaw

/-- The probability of remaining in a corridor throughout a complete
segment is invariant under deterministic time translation. -/
theorem HasIndepIncrements.measure_fullSegmentCorridor_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hindep : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
    (start length : ℝ≥0) (lower upper : ℝ) :
    P (fullSegmentCorridorEvent X 0 length lower upper) =
      P (fullSegmentCorridorEvent X start length lower upper) := by
  let A : Set Ω :=
    (fun ω q => X (length * RationalCoordinate.toNNReal q) ω - X 0 ω) ⁻¹'
      Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  let B : Set Ω :=
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω -
      X start ω) ⁻¹' Skorokhod.rationalCoordinateCorridorWithMargin lower upper
  have hlaw : P A = P B := by
    exact (centeredRationalSegment_identDistrib hindep hstationary start length).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin lower upper)
  have haeA : A =ᵐ[P] fullSegmentCorridorEvent X 0 length lower upper := by
    filter_upwards [hcadlag] with ω hω
    simpa [A, zero_add] using propext
      (mem_fullSegmentCorridorEvent_iff_rational
        X 0 length lower upper ω hω).symm
  have haeB : B =ᵐ[P] fullSegmentCorridorEvent X start length lower upper := by
    filter_upwards [hcadlag] with ω hω
    exact propext (mem_fullSegmentCorridorEvent_iff_rational
      X start length lower upper ω hω).symm
  rw [measure_congr haeA, measure_congr haeB] at hlaw
  exact hlaw

/-- The probability of remaining in a corridor and ending in a prescribed
return window is invariant under deterministic time translation. -/
theorem HasIndepIncrements.measure_fullSegmentCorridorReturn_shift
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hindep : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω))
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
    (fun ω q => X (start + length * RationalCoordinate.toNNReal q) ω -
      X start ω) ⁻¹' Skorokhod.rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper
  have hlaw : P A = P B := by
    exact (centeredRationalSegment_identDistrib hindep hstationary start length).measure_mem_eq
      (Skorokhod.measurableSet_rationalCoordinateCorridorReturnWithMargin
        lower upper coreLower coreUpper)
  have haeA : A =ᵐ[P] fullSegmentCorridorReturnEvent X 0 length
      lower upper coreLower coreUpper := by
    filter_upwards [hcadlag] with ω hω
    simpa [A, zero_add] using propext
      (mem_fullSegmentCorridorReturnEvent_iff_rational
        X 0 length lower upper coreLower coreUpper ω hω).symm
  have haeB : B =ᵐ[P] fullSegmentCorridorReturnEvent X start length
      lower upper coreLower coreUpper := by
    filter_upwards [hcadlag] with ω hω
    exact propext (mem_fullSegmentCorridorReturnEvent_iff_rational
      X start length lower upper coreLower coreUpper ω hω).symm
  rw [measure_congr haeA, measure_congr haeB] at hlaw
  exact hlaw

end ProbabilityTheory

end

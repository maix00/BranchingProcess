/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Step.Ordering.Law
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# One-slot moment assumptions on the child law

The leftmost-child assumptions use a `StepLaw` ordering rule before reading
slot zero. The raw law itself is not required to be ordered; the symmetric
cross-child weight condition lives separately in `CrossWeight.lean`.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory

def StepLaw.leftmostPositivePart {ι α X : Type*} [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) (ξ : Combinatorics.Branching.Step ι X) : ℝ :=
  max (L.displacement ⊥ ξ) 0

def StepLaw.leftmostNegativePart {ι α X : Type*} [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) (ξ : Combinatorics.Branching.Step ι X) : ℝ :=
  max (-(L.displacement ⊥ ξ)) 0

theorem StepLaw.leftmostPositivePart_measurable
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) :
    Measurable L.leftmostPositivePart :=
  (L.displacement_measurable ⊥).max measurable_const

theorem StepLaw.leftmostNegativePart_measurable
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) :
    Measurable L.leftmostNegativePart := by
  exact (L.displacement_measurable ⊥).neg.max measurable_const

/-- Boundary normalization controls the negative part of the ordered
leftmost displacement. The ordering preserves the total exponential weight,
so the fixed-slot estimate applies to its least slot. -/
theorem StepLaw.integrable_leftmostNegativePart
    {ι α X : Type*} [Countable ι] [Countable α] [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X)
    (hboundary : HasBoundaryNormalization L.potential L.raw) :
    Integrable L.leftmostNegativePart L.raw := by
  have hsortedBoundary := L.sorted_hasBoundaryNormalization hboundary
  have hsorted : Integrable
      (fun ξ : Combinatorics.Branching.Step α X =>
        max (-(ξ.potentialValue' L.potential ⊥)) 0) L.sorted :=
    hsortedBoundary.integrable_negativePotentialValue L.potential L.sorted ⊥
  have hcomp :
      (fun ξ : Combinatorics.Branching.Step ι X =>
        max (-((L.ordering ξ).potentialValue' L.potential ⊥)) 0) =
      L.leftmostNegativePart := rfl
  rw [← hcomp]
  exact (integrable_map_measure hsorted.aestronglyMeasurable
    L.ordering.measurable_ordered.aemeasurable).mp hsorted

def HasLeftmostFirstMoment {ι α X : Type*} [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  Integrable L.leftmostPositivePart L.raw

/-- The positive-part assumption and boundary normalization together give a
full first moment for the ordered leftmost displacement. The positive part
is the explicit moment hypothesis; the negative part follows from the
exponential weight bound. -/
theorem StepLaw.integrable_leftmostDisplacement
    {ι α X : Type*} [Countable ι] [Countable α] [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L) :
    Integrable (fun ξ => L.displacement ⊥ ξ) L.raw := by
  change Integrable L.leftmostPositivePart L.raw at hfirst
  have hnegative := L.integrable_leftmostNegativePart hboundary
  have hidentity : (fun ξ => L.displacement ⊥ ξ) =
      fun ξ => L.leftmostPositivePart ξ - L.leftmostNegativePart ξ := by
    funext ξ
    by_cases h : 0 ≤ L.displacement ⊥ ξ
    · simp [StepLaw.leftmostPositivePart, StepLaw.leftmostNegativePart,
        max_eq_left h, max_eq_right (by linarith : -L.displacement ⊥ ξ ≤ 0)]
    · have h' : L.displacement ⊥ ξ ≤ 0 := le_of_not_ge h
      simp [StepLaw.leftmostPositivePart, StepLaw.leftmostNegativePart,
        max_eq_right h', max_eq_left (by linarith : 0 ≤ -L.displacement ⊥ ξ)]
  rw [hidentity]
  exact hfirst.sub hnegative

/-- The ordered child law has an integrable bottom-slot displacement whenever
the raw `StepLaw` satisfies the leftmost first-moment and boundary
normalization assumptions. -/
theorem StepLaw.integrable_sortedLeftmostDisplacement
    {ι α X : Type*} [Countable ι] [Countable α] [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L) :
    Integrable (fun ξ : Combinatorics.Branching.Step α X =>
      ξ.potentialValue' L.potential ⊥) L.sorted := by
  have hraw : Integrable
      (fun ξ : Combinatorics.Branching.Step ι X =>
        (L.ordering ξ).potentialValue' L.potential ⊥) L.raw := by
    simpa [StepLaw.displacement] using
      L.integrable_leftmostDisplacement hboundary hfirst
  rw [StepLaw.sorted]
  exact (integrable_map_measure
    (Step.potentialValue'_measurable L.potential ⊥).aestronglyMeasurable
    L.ordering.measurable_ordered.aemeasurable).mpr hraw

/-- The paper's positive first moment, together with boundary normalization,
gives an integrable absolute first slot after sorting and projecting marks
through the potential. This is the one-step input for the Kingman argument. -/
theorem StepLaw.integrable_sortedPotentialImage_firstSlot_abs
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (L : StepLaw ι ℕ X)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L) :
    Integrable (fun ξ : Combinatorics.Branching.Step ℕ ℝ =>
      |value' ξ 0|) L.sortedPotentialImage := by
  let f : Combinatorics.Branching.Step ℕ ℝ → ℝ := fun ξ => |value' ξ 0|
  have hf : Measurable f := by
    exact Measurable.abs (value'_measurable (0 : ℕ))
  have hsorted : Integrable
      (fun ξ : Combinatorics.Branching.Step ℕ X =>
        |ξ.potentialValue' L.potential 0|) L.sorted := by
    exact (L.integrable_sortedLeftmostDisplacement hboundary hfirst).abs
  have hcompose : Integrable
      (fun ξ : Combinatorics.Branching.Step ℕ X =>
        f (ξ.map L.potential)) L.sorted := by
    have hEq : (fun ξ : Combinatorics.Branching.Step ℕ X =>
        f (ξ.map L.potential)) =
        fun ξ => |ξ.potentialValue' L.potential 0| := by
      funext ξ
      have hvalue : value' (ξ.map L.potential) 0 =
          ξ.potentialValue' L.potential 0 := by
        change ((ξ.map L.potential) 0).getD 0 = _
        rw [Step.map_apply]
        rfl
      simp [f, hvalue]
    rw [hEq]
    exact hsorted
  change Integrable f
    (L.sorted.map (fun ξ : Combinatorics.Branching.Step ℕ X =>
      ξ.map L.potential))
  exact (integrable_map_measure hf.aestronglyMeasurable
    (Step.map_measurable L.potential.measurable_toFun).aemeasurable).mpr hcompose

def HasLeftmostFourthMoment {ι α X : Type*} [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  Integrable (fun ξ => (L.leftmostPositivePart ξ) ^ 4) L.raw

def HasLeftmostPositiveExponentialMoment
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Integrable (fun ξ => Real.exp (c * L.displacement ⊥ ξ)) L.raw

theorem fourthMoment_implies_firstMoment
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) [IsFiniteMeasure L.raw]
    (h : HasLeftmostFourthMoment L) :
    HasLeftmostFirstMoment L := by
  have hmeas : AEStronglyMeasurable L.leftmostPositivePart L.raw := by
    exact L.leftmostPositivePart_measurable.aestronglyMeasurable
  apply ((integrable_const (1 : ℝ)).add h).mono hmeas
  filter_upwards [] with ξ
  have hx : 0 ≤ L.leftmostPositivePart ξ := le_max_right _ _
  change |L.leftmostPositivePart ξ| ≤ |1 + L.leftmostPositivePart ξ ^ 4|
  rw [abs_of_nonneg hx,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + L.leftmostPositivePart ξ ^ 4)]
  by_cases hle : L.leftmostPositivePart ξ ≤ 1
  · nlinarith [pow_nonneg hx 4]
  · have hone : 1 ≤ L.leftmostPositivePart ξ := le_of_not_ge hle
    have hquad : 0 ≤ L.leftmostPositivePart ξ ^ 2 +
        L.leftmostPositivePart ξ + 1 := by
      nlinarith [sq_nonneg (L.leftmostPositivePart ξ)]
    have hprod : 0 ≤ L.leftmostPositivePart ξ *
        (L.leftmostPositivePart ξ - 1) *
        (L.leftmostPositivePart ξ ^ 2 + L.leftmostPositivePart ξ + 1) :=
      mul_nonneg (mul_nonneg hx (sub_nonneg.mpr hone)) hquad
    nlinarith

end ProbabilityTheory.BranchingRandomWalk

end

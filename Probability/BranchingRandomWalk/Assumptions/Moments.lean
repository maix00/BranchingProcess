/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

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

theorem StepLaw.leftmostPositivePart_measurable
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) :
    Measurable L.leftmostPositivePart :=
  (L.displacement_measurable ⊥).max measurable_const

def HasLeftmostFirstMoment {ι α X : Type*} [MeasurableSpace X]
    [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  Integrable L.leftmostPositivePart L.raw

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

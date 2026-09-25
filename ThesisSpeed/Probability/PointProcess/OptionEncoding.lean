import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued offspring encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  It is kept separate from the legacy weighted
slot implementation so that the latter can be migrated without changing the
pre-sampled-tree API in one step.
-/

open MeasureTheory
open Classical

namespace ThesisSpeed

abbrev BranchingStep (ι X : Type*) := ι → Option X

def branchingStepPresent {ι X : Type*}
    (ξ : BranchingStep ι X) (i : ι) : Prop := ∃ x, ξ i = some x

def branchingStepPrefixOrdered {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  ∀ i j x y, i < j → ξ i = some x → ξ j = some y → x ≤ y

def branchingStepPresencePrefix {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X) : Prop :=
  ∀ i j, i < j → ξ i = none → ξ j = none

def OrderedBranchingStep {ι X : Type*} [LT ι] [LE X]
    (ξ : BranchingStep ι X) : Prop :=
  branchingStepPresencePrefix ξ ∧ branchingStepPrefixOrdered ξ

theorem branchingStep_present_of_later
    {ι X : Type*} [LT ι]
    (ξ : BranchingStep ι X)
    (hprefix : branchingStepPresencePrefix ξ)
    {i j : ι} (hij : i < j) (h : branchingStepPresent ξ j) :
    branchingStepPresent ξ i := by
  classical
  by_contra hi
  simp only [branchingStepPresent, not_exists] at hi
  have hnone : ξ i = none := by
    cases hxi : ξ i with
    | none => simpa [hxi]
    | some x => exact (hi x hxi).elim
  obtain ⟨y, hy⟩ := h
  have hjnone := hprefix i j hij hnone
  rw [hy] at hjnone
  cases hjnone

abbrev NatRealBranchingStep := BranchingStep ℕ ℝ

def branchingStepChildPresent (ξ : NatRealBranchingStep) (i : ℕ) : Prop :=
  branchingStepPresent ξ i

def branchingStepNatRealOrdered (ξ : NatRealBranchingStep) : Prop :=
  branchingStepPrefixOrdered ξ

def branchingStepNatRealPresencePrefix (ξ : NatRealBranchingStep) : Prop :=
  branchingStepPresencePrefix ξ

def OrderedNatRealBranchingStep (ξ : NatRealBranchingStep) : Prop :=
  OrderedBranchingStep ξ

noncomputable def branchingStepAtomMeasure (ξ : NatRealBranchingStep) (i : ℕ) :
    Measure ℝ := by
  classical
  exact match ξ i with
  | some x => Measure.dirac x
  | none => 0

noncomputable def branchingStepPointMeasure (ξ : NatRealBranchingStep) :
    Measure ℝ := Measure.sum (branchingStepAtomMeasure ξ)

theorem branchingStepAtomMeasure_apply (ξ : NatRealBranchingStep) (i : ℕ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    branchingStepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  classical
  cases h : ξ i with
  | none => simp [branchingStepAtomMeasure, h]
  | some x =>
      by_cases hx : x ∈ s <;>
        simp [branchingStepAtomMeasure, h, Measure.dirac_apply' _ hs, hx]

theorem branchingStepPointMeasure_apply (ξ : NatRealBranchingStep)
    (s : Set ℝ) (hs : MeasurableSet s) :
    branchingStepPointMeasure ξ s =
      ∑' i : ℕ, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [branchingStepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => branchingStepAtomMeasure_apply ξ i s hs)

end ThesisSpeed

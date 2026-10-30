/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Potential
public import MeasureTheory.BranchingWalk.Step.Selection.FirstN
public import MeasureTheory.BranchingWalk.Step.Selection.Slot
import MeasureTheory.MeasurableSpace.Finset.Filter
import MeasureTheory.MeasurableSpace.CountableEvaluation

/-!
# Measurability of potential-based branching selections

These results place the measure-theoretic properties beside the combinatorial
potential and slot selectors.

## Public declarations

- `Combinatorics.Branching.Step.FiniteSelection.belowPotential_measurable`
  proves measurability after removing selected children above a potential
  cutoff.
- `Combinatorics.Branching.Step.FiniteSelection.firstOnlySelectedChild_measurable`
  and `reserveSelectionBelowPotential_measurable` prove measurability of the
  first-child and reserve selectors.
- `Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlotPositivePotential_measurable`
  proves that the positive potential of the first selected child is measurable
  when the step selection is measurable.
- `Combinatorics.Branching.Step.FiniteSelection.preserveFirstBelowPotential_measurable`
  proves measurability of the first-child-preserving intrinsic potential
  selection.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching.Step.FiniteSelection

open _root_.Combinatorics.Selection.NSelection
open _root_.MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

theorem firstSelectedSlotPositivePotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) :
    Measurable (firstSelectedSlotPositivePotential R φ) := by
  have hfirst := firstSelectedSlot_measurable R hR
  have hcoordinate (i : α) (_hi : i ∈ Set.range (firstSelectedSlot R)) :
      Measurable (fun ξ : Step α X => ξ.potentialValue' φ i) :=
    Step.potentialValue'_measurable φ i
  have hfiber (i : α) (_hi : i ∈ Set.range (firstSelectedSlot R)) :
      MeasurableSet {ξ : Step α X | firstSelectedSlot R ξ = i} := by
    have hfiber' : MeasurableSet
        ((firstSelectedSlot R) ⁻¹' ({i} : Set α)) :=
      hfirst (measurableSet_singleton i)
    have heq : {ξ : Step α X | firstSelectedSlot R ξ = i} =
        (firstSelectedSlot R) ⁻¹' ({i} : Set α) := by
      ext ξ
      rfl
    rw [heq]
    exact hfiber'
  have hvalue : Measurable (fun ξ : Step α X =>
      ξ.potentialValue' φ (firstSelectedSlot R ξ)) :=
    Measurable.eval_of_countable_range
      (fun ξ i => ξ.potentialValue' φ i) (firstSelectedSlot R)
      hcoordinate hfiber (Set.to_countable _)
  change Measurable (fun ξ : Step α X =>
    max 0 (ξ.potentialValue' φ (firstSelectedSlot R ξ)))
  exact measurable_const.max hvalue

theorem belowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (a : ℝ) :
    Measurable (R.belowPotential φ a).select := by
  apply hR.finset_filter (fun ξ i => ξ.potentialValue' φ i ≤ a)
  intro i
  exact measurableSet_setOfPred.mp
    ((Step.potentialValue'_measurable φ i) measurableSet_Iic)

theorem firstOnlySelectedChild_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    Measurable (firstOnlySelectedChild R).select := by
  apply hR.finset_filter (fun ξ i => i = firstSelectedSlot R ξ)
  intro i
  have hfirst := firstSelectedSlot_measurable R hR
  have hset : {ξ : Step α X | i = firstSelectedSlot R ξ} =
      (firstSelectedSlot R) ⁻¹' ({i} : Set α) := by
    ext ξ
    simp [eq_comm]
  apply measurableSet_setOfPred.mp
  rw [hset]
  exact hfirst (measurableSet_singleton i)

theorem reserveSelectionBelowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (M : ℝ) :
    Measurable (reserveSelectionBelowPotential R φ M).select := by
  let first := firstOnlySelectedChild R
  let bounded := R.belowPotential φ M
  have hfirst : Measurable first.select := by
    simpa [first] using firstOnlySelectedChild_measurable R hR
  have hbounded : Measurable bounded.select := by
    simpa [bounded] using belowPotential_measurable R hR φ M
  have hunion : Measurable (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    measurable_of_countable _
  have h := hunion.comp (hfirst.prodMk hbounded)
  simpa [Function.comp_def, reserveSelectionBelowPotential, first, bounded] using h

theorem preserveFirstBelowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    Measurable
      (Step.FiniteSelection.preserveFirstBelowPotential
        N φ a hlevel).select := by
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => Step.FiniteSelection.admitsFirstNByPotential_of_level_finite
      k φ ξ (hlevel ξ)
  let first := Step.FiniteSelection.firstNByPotential 1 φ (admits 1)
  let initial := Step.FiniteSelection.firstNByPotential N φ (admits N)
  have hfirst : Measurable first.select := firstNByPotential_measurable 1 φ (admits 1)
  have hinitial : Measurable initial.select := firstNByPotential_measurable N φ (admits N)
  have hbelow : Measurable (initial.belowPotential φ a).select :=
    belowPotential_measurable initial hinitial φ a
  have hunion : Measurable
      (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    measurable_of_countable _
  have h := hunion.comp (hfirst.prodMk hbelow)
  change Measurable (fun ξ => first ξ ∪ (initial.belowPotential φ a) ξ) at h
  simpa only [Step.FiniteSelection.preserveFirstBelowPotential,
    first, initial, admits] using h

end Combinatorics.Branching.Step.FiniteSelection

end

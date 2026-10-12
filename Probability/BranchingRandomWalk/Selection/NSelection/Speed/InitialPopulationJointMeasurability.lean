/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
import Probability.BranchingRandomWalk.Selection.NSelection.Speed.SelectedPopulationBatch

/-!
# Measurability with a random initial population

The totalized selected population at a fixed generation is measurable jointly
in its initial position vector and its pre-sampled field.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def selectedPopulationWithParameter
    (N n : ℕ)
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) →
      Finset (RootIndexed.TreeNode (Fin N) ℕ) :=
  fun p => RootIndexed.selectedPopulationTotalized N Finset.univ p.1 id id n p.2

private theorem measurable_observedPositionWithParameter
    (N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (q : RootIndexed.TreeNode (Fin N) ℕ) :
    Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      RootIndexed.observedPositionAtGeneration p.1 id id n p.2 q) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin N) (α := ℕ) (X := ℝ)
  by_cases hdepth : q.2.length = n
  · have hdisp : Measurable (fun field : RootIndexed.StepField (Fin N) ℕ ℝ =>
        Combinatorics.Branching.displaceWith (fun x : ℝ => x)
          (field q.1) [] q.2) := by
      have h := RootIndexed.displace_measurable (fun x : ℝ => x) measurable_id
        q.1 [] q.2 n (by simp [hdepth])
      exact h.mono (F.le n) le_rfl
    have hdisp' : Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
          Combinatorics.Branching.displaceWith (fun x : ℝ => x)
            (p.2 q.1) [] q.2) := hdisp.comp measurable_snd
    have hinitial : Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ => p.1 q.1) :=
      (measurable_pi_apply q.1).comp measurable_fst
    change Measurable (fun p :
      (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      RootIndexed.positionAtGeneration p.1 id n q.1 q.2 p.2)
    simp only [RootIndexed.positionAtGeneration, hdepth, if_pos,
      RootIndexed.position]
    exact hinitial.add hdisp'
  · change Measurable (fun p :
      (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      RootIndexed.positionAtGeneration p.1 id n q.1 q.2 p.2)
    simp [RootIndexed.positionAtGeneration, hdepth]

private theorem measurable_childrenAtGenerationWithParameter
    (N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (parents : ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) →
      Finset (RootIndexed.TreeNode (Fin N) ℕ))
    (hparents : Measurable parents) :
    Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
      RootIndexed.childrenAtGeneration n (parents p) p.2) := by
  classical
  rw [measurable_set_iff]
  intro q
  by_cases hdepth : q.2.length = n + 1
  · have hnonempty : q.2 ≠ [] := by
      intro h
      simp [h] at hdepth
    let j := q.2.getLast hnonempty
    have hlast : q.2.getLast? = some j :=
      List.getLast?_eq_some_getLast hnonempty
    have hparent : Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
          parent q ∈ parents p) :=
      (measurable_finset_mem (parent q)).comp hparents
    have hmark : Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
          p.2 (parent q).1 (parent q).2) :=
      (measurable_pi_apply (parent q).2).comp
        ((measurable_pi_apply (parent q).1).comp measurable_snd)
    have hsurvive : MeasurableSet {p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
          survive (p.2 (parent q).1 (parent q).2) j} :=
      (survive_measurableSet j).preimage hmark
    change Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
          q ∈ RootIndexed.childrenAtGeneration n (parents p) p.2)
    simp only [RootIndexed.childrenAtGeneration, Set.mem_setOf_eq, hdepth, hlast]
    simp only [true_and]
    exact hparent.and (measurableSet_setOfPred.mp hsurvive)
  · change Measurable (fun p :
      (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
        q ∈ RootIndexed.childrenAtGeneration n (parents p) p.2)
    simp [RootIndexed.childrenAtGeneration, Set.mem_setOf_eq, hdepth]

/-- The totalized selected population is measurable jointly in its initial
position vector and the pre-sampled field, at every finite generation. -/
theorem measurable_selectedPopulationWithParameter
    (N : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    ∀ n, Measurable (selectedPopulationWithParameter N n) := by
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder
  letI : Preorder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder.toPreorder
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let parents := selectedPopulationWithParameter N n
      have hchildren := measurable_childrenAtGenerationWithParameter
        N n parents ih
      let value : ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) →
          RootIndexed.TreeNode (Fin N) ℕ → ℝ := fun p =>
        RootIndexed.observedPositionAtGeneration p.1 id id (n + 1) p.2
      have hvalue (q : RootIndexed.TreeNode (Fin N) ℕ) :
          Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
            value p q) := by
        simpa [value] using measurable_observedPositionWithParameter N (n + 1) q
      have hkey (p q : RootIndexed.TreeNode (Fin N) ℕ) : Measurable
          (fun x : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
            valueKey (value x) q < valueKey (value x) p) := by
        exact @NSelection.measurable_valueKey_lt
          ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ)
          (RootIndexed.TreeNode (Fin N) ℕ) ℝ _ _ _ _ _ _ _ _ treeOrder
          value hvalue p q
      have hselected := @NSelection.measurable_selectFirstNFromSetTotalized
        ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ)
        (RootIndexed.TreeNode (Fin N) ℕ) ℝ inferInstance inferInstance
        treeOrder inferInstance N value
        (fun x => RootIndexed.childrenAtGeneration n (parents x) x.2)
        hchildren hkey
      change Measurable (fun p :
        (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
        NSelection.selectFirstNFromSetTotalized N
          (fun p => RootIndexed.observedPositionAtGeneration p.1 id id
            (n + 1) p.2)
          (fun p => RootIndexed.childrenAtGeneration n
            (RootIndexed.selectedPopulationTotalized N Finset.univ
              p.1 id id n p.2) p.2) p)
      exact hselected

/-- The leftmost position in a totalized selected population, set to zero
when the selected set is empty. This endpoint is measurable jointly in the
initial position vector and the pre-sampled field. -/
noncomputable def selectedPopulationEndpointWithParameter
    (N n : ℕ)
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)]
    (p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) : ℝ := by
  classical
  let population := selectedPopulationWithParameter N n p
  let value := RootIndexed.observedPositionAtGeneration p.1 id id n p.2
  exact if h : population.Nonempty then population.inf' h value else 0

theorem measurable_selectedPopulationEndpointWithParameter
    (N n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin N) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin N) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin N) ℕ)]
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ)] :
    Measurable (selectedPopulationEndpointWithParameter N n) := by
  classical
  letI : LinearOrder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder
  letI : Preorder (RootIndexed.TreeNode (Fin N) ℕ) := treeOrder.toPreorder
  let population := selectedPopulationWithParameter N n
  let value : ((Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ) →
      RootIndexed.TreeNode (Fin N) ℕ → ℝ := fun p =>
        RootIndexed.observedPositionAtGeneration p.1 id id n p.2
  have hpopulation : Measurable population :=
    measurable_selectedPopulationWithParameter N _
  have hvalue (q : RootIndexed.TreeNode (Fin N) ℕ) :
      Measurable (fun p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ =>
        value p q) := by
    simpa [value] using measurable_observedPositionWithParameter N n q
  apply measurable_of_Iic
  intro x
  have hbelow : {p | selectedPopulationEndpointWithParameter N n p ≤ x} =
      (⋃ q : RootIndexed.TreeNode (Fin N) ℕ,
        {p | q ∈ population p ∧ value p q ≤ x}) ∪
      (if 0 ≤ x then {p | population p = ∅} else ∅) := by
    ext p
    change selectedPopulationEndpointWithParameter N n p ≤ x ↔ _
    by_cases hne : (population p).Nonempty
    · have hnotEmpty : population p ≠ ∅ := hne.ne_empty
      rw [show selectedPopulationEndpointWithParameter N n p =
        (population p).inf' hne (value p) by
          simp [selectedPopulationEndpointWithParameter, population, value, hne]]
      simp [Finset.inf'_le_iff, hnotEmpty, Set.mem_iUnion]
    · have hempty : population p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [selectedPopulationEndpointWithParameter, population, value, hempty]
  change MeasurableSet
    {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
      selectedPopulationEndpointWithParameter N n p ≤ x}
  rw [hbelow]
  have hterms : MeasurableSet
      (⋃ q : RootIndexed.TreeNode (Fin N) ℕ,
        {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
          q ∈ population p ∧ value p q ≤ x}) := by
    apply MeasurableSet.iUnion
    intro q
    have hmem : MeasurableSet
        {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
          q ∈ population p} := hpopulation (measurableSet_mem_finset q)
    have hvalueBelow : MeasurableSet
        {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
          value p q ≤ x} := measurableSet_Iic.preimage (hvalue q)
    exact hmem.inter hvalueBelow
  have hempty : MeasurableSet
      {p : (Fin N → ℝ) × RootIndexed.StepField (Fin N) ℕ ℝ |
        population p = ∅} := hpopulation (measurableSet_singleton ∅)
  by_cases hx : 0 ≤ x
  · simp only [if_pos hx]
    exact hterms.union hempty
  · simp only [if_neg hx]
    exact hterms.union MeasurableSet.empty

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

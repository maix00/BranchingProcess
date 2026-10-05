/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtree

/-!
# Coordinates inspected by an exploration

An exploration domain is bounded by the branching-step coordinates actually
inspected. Coordinates over disjoint address sets are independent, and a
descendant address set disjoint from the inspected coordinates stays fresh.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


@[instance_reducible] def stepsOnSpace
    {α X : Type*} [MeasurableSpace X] (s : Set (TreeNode α)) :
    MeasurableSpace (TreeNode α → Step α X) :=
  ⨆ u ∈ s, stepCoordinateSpace u

theorem stepsOnSpace_mono
    {α X : Type*} [MeasurableSpace X] {s t : Set (TreeNode α)} (hst : s ⊆ t) :
    stepsOnSpace (X := X) s ≤ stepsOnSpace t := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem stepsOnSpace_le
    {α X : Type*} [MeasurableSpace X] (s : Set (TreeNode α)) :
    stepsOnSpace (X := X) s ≤
      (inferInstance : MeasurableSpace (TreeNode α → Step α X)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  exact (measurable_pi_apply u).comap_le

theorem stepsOnSpace_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (s t : Set (TreeNode α)) (hdisj : Disjoint s t) :
    Indep (stepsOnSpace s) (stepsOnSpace t)
      (stepFieldLaw μ) := by
  have hle : ∀ u : TreeNode α, stepCoordinateSpace (X := X) u ≤
      (inferInstance : MeasurableSpace (TreeNode α → Step α X)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle
    (step_coordinate_independent μ) hdisj

theorem stepsOnSpace_descendant_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (explored : Set (TreeNode α)) (root : TreeNode α)
    (hfresh : Disjoint explored (branchingDescendantAddresses root)) :
    Indep (stepsOnSpace explored)
      (stepDescendantSpace root) (stepFieldLaw μ) := by
  rw [stepDescendantSpace_eq_iSup]
  exact stepsOnSpace_independent μ explored
    (branchingDescendantAddresses root) hfresh

end ProbabilityTheory.BranchingRandomWalk

end

import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtree

/-!
# Coordinates inspected by an exploration

An exploration domain is bounded by the branching-step coordinates actually
inspected. Coordinates over disjoint address sets are independent, and a
descendant address set disjoint from the inspected coordinates stays fresh.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


@[instance_reducible] def stepsOnSpace
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    MeasurableSpace (𝕍 → Step ℕ X) :=
  ⨆ u ∈ s, stepCoordinateSpace u

theorem stepsOnSpace_mono
    {X : Type*} [MeasurableSpace X] {s t : Set 𝕍} (hst : s ⊆ t) :
    stepsOnSpace (X := X) s ≤ stepsOnSpace t := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem stepsOnSpace_le
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    stepsOnSpace (X := X) s ≤
      (inferInstance : MeasurableSpace (𝕍 → Step ℕ X)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  exact (measurable_pi_apply u).comap_le

theorem stepsOnSpace_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (s t : Set 𝕍) (hdisj : Disjoint s t) :
    Indep (stepsOnSpace s) (stepsOnSpace t)
      (stepFieldLaw μ) := by
  have hle : ∀ u : 𝕍, stepCoordinateSpace (X := X) u ≤
      (inferInstance : MeasurableSpace (𝕍 → Step ℕ X)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle
    (step_coordinate_independent μ) hdisj

theorem stepsOnSpace_descendant_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (explored : Set 𝕍) (root : 𝕍)
    (hfresh : Disjoint explored (branchingDescendantAddresses root)) :
    Indep (stepsOnSpace explored)
      (stepDescendantSpace root) (stepFieldLaw μ) := by
  rw [stepDescendantSpace_eq_iSup]
  exact stepsOnSpace_independent μ explored
    (branchingDescendantAddresses root) hfresh

end ProbabilityTheory.BranchingRandomWalk

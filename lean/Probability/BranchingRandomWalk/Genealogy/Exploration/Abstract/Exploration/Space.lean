import Probability.BranchingRandomWalk.Genealogy.Exploration.Selected.AbstractSubtree

/-!
# Coordinates inspected by an exploration

An exploration domain is bounded by the branching-step coordinates actually
inspected. Coordinates over disjoint address sets are independent, and a
descendant address set disjoint from the inspected coordinates stays fresh.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory


@[instance_reducible] def branchingStepsOnSpace
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  ⨆ u ∈ s, branchingStepCoordinateSpace u

theorem branchingStepsOnSpace_mono
    {X : Type*} [MeasurableSpace X] {s t : Set 𝕍} (hst : s ⊆ t) :
    branchingStepsOnSpace (X := X) s ≤ branchingStepsOnSpace t := by
  apply iSup_le
  intro u
  apply iSup_le
  intro hu
  exact le_iSup_of_le u (le_iSup_of_le (hst hu) le_rfl)

theorem branchingStepsOnSpace_le
    {X : Type*} [MeasurableSpace X] (s : Set 𝕍) :
    branchingStepsOnSpace (X := X) s ≤
      (inferInstance : MeasurableSpace (𝕍 → BranchingStep ℕ X)) := by
  apply iSup_le
  intro u
  apply iSup_le
  intro _
  exact (measurable_pi_apply u).comap_le

theorem branchingStepsOnSpace_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (s t : Set 𝕍) (hdisj : Disjoint s t) :
    Indep (branchingStepsOnSpace s) (branchingStepsOnSpace t)
      (branchingStepFieldLaw μ) := by
  have hle : ∀ u : 𝕍, branchingStepCoordinateSpace (X := X) u ≤
      (inferInstance : MeasurableSpace (𝕍 → BranchingStep ℕ X)) :=
    fun u => (measurable_pi_apply u).comap_le
  exact indep_iSup_of_disjoint hle
    (branchingStep_coordinate_independent μ) hdisj

theorem branchingStepsOnSpace_descendant_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (explored : Set 𝕍) (root : 𝕍)
    (hfresh : Disjoint explored (branchingDescendantAddresses root)) :
    Indep (branchingStepsOnSpace explored)
      (branchingStepDescendantSpace root) (branchingStepFieldLaw μ) := by
  rw [branchingStepDescendantSpace_eq_iSup]
  exact branchingStepsOnSpace_independent μ explored
    (branchingDescendantAddresses root) hfresh

end ProbabilityTheory.BranchingRandomWalk

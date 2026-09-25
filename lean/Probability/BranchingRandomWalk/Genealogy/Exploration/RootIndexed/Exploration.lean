import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence

/-!
# Exploration domains for several initial roots

Coordinates are labelled by an initial-root index and a local Ulam--Harris
address.  A reserve subtree is fresh whenever its complete descendant address
set is disjoint from the coordinates inspected by the exploration.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



@[instance_reducible] def multiRootBranchingStepsOnSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (s : Set (Fin m × 𝕍)) :
    MeasurableSpace (FiniteRootBranchingStepField m X) :=
  ⨆ p ∈ s, multiRootStepCoordinateSpace p

def multiRootDescendantAddresses {m : ℕ}
    (root : Fin m × 𝕍) : Set (Fin m × 𝕍) :=
  {p | ∃ tail : 𝕍, p = (root.1, root.2 ++ tail)}

@[instance_reducible] def multiRootDescendantStepSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (root : Fin m × 𝕍) :
    MeasurableSpace (FiniteRootBranchingStepField m X) :=
  ⨆ tail : 𝕍,
    multiRootStepCoordinateSpace (root.1, root.2 ++ tail)

def multiRootAddressSubtreeStepField
    {m : ℕ} {X : Type*} (root : Fin m × 𝕍)
    (step : FiniteRootBranchingStepField m X) : 𝕍 → BranchingStep ℕ X :=
  fun tail => step root.1 (root.2 ++ tail)

theorem multiRootDescendantStepSpace_eq_iSup
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (root : Fin m × 𝕍) :
    multiRootDescendantStepSpace (X := X) root =
      multiRootBranchingStepsOnSpace
        (multiRootDescendantAddresses root) := by
  apply le_antisymm
  · apply iSup_le
    intro tail
    exact le_iSup_of_le (root.1, root.2 ++ tail)
      (le_iSup_of_le ⟨tail, rfl⟩ le_rfl)
  · apply iSup_le
    intro p
    apply iSup_le
    rintro ⟨tail, rfl⟩
    exact le_iSup (fun v : 𝕍 =>
      multiRootStepCoordinateSpace (X := X)
        (root.1, root.2 ++ v)) tail

theorem multiRootBranchingStepsOnSpace_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (s t : Set (Fin m × 𝕍)) (hdisj : Disjoint s t) :
    Indep (multiRootBranchingStepsOnSpace s)
      (multiRootBranchingStepsOnSpace t) (finiteRootBranchingStepFieldLaw μ m) := by
  have hle : ∀ p : Fin m × 𝕍,
      multiRootStepCoordinateSpace (X := X) p ≤
        (inferInstance : MeasurableSpace (FiniteRootBranchingStepField m X)) := by
    intro p
    have hmeas : Measurable
        (fun step : FiniteRootBranchingStepField m X => step p.1 p.2) :=
      (measurable_pi_apply p.2 : Measurable
        (fun field : 𝕍 → BranchingStep ℕ X => field p.2)).comp
        (measurable_pi_apply p.1 : Measurable
          (fun step : FiniteRootBranchingStepField m X => step p.1))
    exact hmeas.comap_le
  exact indep_iSup_of_disjoint hle
    (multiRootStep_coordinates_independent μ) hdisj

structure MultiRootBranchingExplorationDomains
    (m : ℕ) (X : Type*) [MeasurableSpace X] where
  inspected : ℕ → Set (Fin m × 𝕍)
  domain : ℕ → MeasurableSpace (FiniteRootBranchingStepField m X)
  domain_le : ∀ j, domain j ≤
    multiRootBranchingStepsOnSpace (inspected j)
  inspected_mono : Monotone inspected

theorem MultiRootBranchingExplorationDomains.fresh_descendant_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : MultiRootBranchingExplorationDomains m X)
    (j : ℕ) (root : Fin m × 𝕍)
    (hfresh : Disjoint (H.inspected j)
      (multiRootDescendantAddresses root)) :
    Indep (H.domain j) (multiRootDescendantStepSpace root)
      (finiteRootBranchingStepFieldLaw μ m) := by
  rw [multiRootDescendantStepSpace_eq_iSup]
  apply indep_of_indep_of_le_left
    (multiRootBranchingStepsOnSpace_independent μ (H.inspected j)
      (multiRootDescendantAddresses root) hfresh)
  exact H.domain_le j

theorem multiRootSubtreeStepField_descendant_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (root : Fin m × 𝕍) :
    Measurable[multiRootDescendantStepSpace root]
      (multiRootAddressSubtreeStepField (X := X) root) := by
  apply (@measurable_pi_iff (FiniteRootBranchingStepField m X) 𝕍
    (fun _ => BranchingStep ℕ X) (multiRootDescendantStepSpace root)
    (fun _ => inferInstance) (multiRootAddressSubtreeStepField root)).2
  intro tail
  have hle : multiRootStepCoordinateSpace (X := X)
      (root.1, root.2 ++ tail) ≤ multiRootDescendantStepSpace root :=
    le_iSup (fun v : 𝕍 => multiRootStepCoordinateSpace
      (X := X) (root.1, root.2 ++ v)) tail
  have hcoord : Measurable[multiRootStepCoordinateSpace (X := X)
      (root.1, root.2 ++ tail)]
      (fun step : FiniteRootBranchingStepField m X =>
        step root.1 (root.2 ++ tail)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem MultiRootBranchingExplorationDomains.fresh_subtree_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (H : MultiRootBranchingExplorationDomains m X)
    (j : ℕ) (root : Fin m × 𝕍)
    (hfresh : Disjoint (H.inspected j)
      (multiRootDescendantAddresses root)) :
    Indep (H.domain j)
      (MeasurableSpace.comap
        (multiRootAddressSubtreeStepField root) inferInstance)
      (finiteRootBranchingStepFieldLaw μ m) :=
  indep_of_indep_of_le_right
    (H.fresh_descendant_independent μ j root hfresh)
    (multiRootSubtreeStepField_descendant_measurable root).comap_le

end ProbabilityTheory.BranchingRandomWalk

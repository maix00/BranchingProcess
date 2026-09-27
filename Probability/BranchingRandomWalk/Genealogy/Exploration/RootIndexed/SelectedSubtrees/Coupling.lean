import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coordinates
import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Generation

/-!
# Spatial coupling of iterated subtree populations

An injective cumulative address map sends any finite population in the
iterated field to a population in the original field.  The resulting clouds
have exactly equal positions, hence the iterated cloud injectively dominates
its embedded original copy for every ordered observation.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling

/-- Map a finite population in an iterated field back to its original
pre-sampled addresses. -/
noncomputable def RootIndexed.iteratedSelectedPopulation
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α X)
    (hinj : Function.Injective
      (RootIndexed.iteratedSelectedAddress chosen j step))
    (population : Finset (RootIndexed.TreeNode Root α)) :
    Finset (RootIndexed.TreeNode Root α) :=
  population.map
    ⟨RootIndexed.iteratedSelectedAddress chosen j step, hinj⟩

@[simp] theorem RootIndexed.mem_iteratedSelectedPopulation
    {Root α X : Type*}
    (chosen : ℕ → RootIndexed.StepField Root α X →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α X)
    (hinj : Function.Injective
      (RootIndexed.iteratedSelectedAddress chosen j step))
    (population : Finset (RootIndexed.TreeNode Root α))
    (q : RootIndexed.TreeNode Root α) :
    q ∈ RootIndexed.iteratedSelectedPopulation
        chosen j step hinj population ↔
      ∃ p ∈ population,
        RootIndexed.iteratedSelectedAddress chosen j step p = q := by
  classical
  simp [RootIndexed.iteratedSelectedPopulation]

/-- The population cloud in an iterated field is spatially identical to its
embedded population cloud in the original field. -/
theorem RootIndexed.iteratedPopulation_injectivelyDominatesBy_original
    {Root α Mark Position Value : Type*}
    [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (initial : Root → Position)
    (d : Mark → Position)
    (chosen : ℕ → RootIndexed.StepField Root α Mark →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α Mark)
    (hinj : Function.Injective
      (RootIndexed.iteratedSelectedAddress chosen j step))
    (population : Finset (RootIndexed.TreeNode Root α)) :
    (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField
          (RootIndexed.iteratedSelectedInitialPosition
            initial d chosen j step)
          (RootIndexed.iteratedSelectedSubtreeStepField chosen j step))
        population).InjectivelyDominatesBy φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial step)
        (RootIndexed.iteratedSelectedPopulation
          chosen j step hinj population)) () := by
  classical
  let address := RootIndexed.iteratedSelectedAddress chosen j step
  refine ⟨address, ?_, hinj.injOn, ?_⟩
  · intro p hp
    change address p ∈ RootIndexed.iteratedSelectedPopulation
      chosen j step hinj population
    exact RootIndexed.mem_iteratedSelectedPopulation
      chosen j step hinj population (address p) |>.2 ⟨p, hp, rfl⟩
  · intro p hp
    change φ (RootIndexed.position initial d step
        (address p).1 (address p).2) ≤
      φ (RootIndexed.position
        (RootIndexed.iteratedSelectedInitialPosition initial d chosen j step) d
        (RootIndexed.iteratedSelectedSubtreeStepField chosen j step)
        p.1 p.2)
    rw [RootIndexed.position_iteratedSelectedAddress]

end ProbabilityTheory.BranchingRandomWalk

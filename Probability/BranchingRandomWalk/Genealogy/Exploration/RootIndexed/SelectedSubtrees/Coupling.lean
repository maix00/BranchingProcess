import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coordinates
import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step

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

/-- The inverse matching from an embedded original population back to its
iterated labels.  It carries the same exact position identity as the forward
embedding and retains concrete slice-map data for later composition. -/
noncomputable def RootIndexed.iteratedOriginalInjection
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
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial step)
        (RootIndexed.iteratedSelectedPopulation
          chosen j step hinj population))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField
          (RootIndexed.iteratedSelectedInitialPosition
            initial d chosen j step)
          (RootIndexed.iteratedSelectedSubtreeStepField chosen j step))
        population) () := by
  classical
  let address := RootIndexed.iteratedSelectedAddress chosen j step
  let back : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun q => if hq : ∃ p ∈ population, address p = q then
      Classical.choose hq
    else q
  have hback {q : RootIndexed.TreeNode Root α}
      (hq : q ∈ RootIndexed.iteratedSelectedPopulation
        chosen j step hinj population) :
      address (back q) = q := by
    have hrange : ∃ p ∈ population, address p = q := by
      simpa [address] using (RootIndexed.mem_iteratedSelectedPopulation
        chosen j step hinj population q).mp hq
    dsimp only [back]
    split
    · exact (Classical.choose_spec ‹∃ p ∈ population, address p = q›).2
    · exact (‹¬ ∃ p ∈ population, address p = q› hrange).elim
  have hbackMem {q : RootIndexed.TreeNode Root α}
      (hq : q ∈ RootIndexed.iteratedSelectedPopulation
        chosen j step hinj population) : back q ∈ population := by
    have hrange : ∃ p ∈ population, address p = q := by
      simpa [address] using (RootIndexed.mem_iteratedSelectedPopulation
        chosen j step hinj population q).mp hq
    dsimp only [back]
    split
    · exact (Classical.choose_spec ‹∃ p ∈ population, address p = q›).1
    · exact (‹¬ ∃ p ∈ population, address p = q› hrange).elim
  refine ⟨back, ?_, ?_, ?_⟩
  · intro q hq
    exact hbackMem hq
  · intro q hq q' hq' heq
    rw [← hback hq, ← hback hq', heq]
  · intro q hq
    have hposition := RootIndexed.position_iteratedSelectedAddress initial d
      chosen j step (back q)
    change φ (RootIndexed.position
        (RootIndexed.iteratedSelectedInitialPosition initial d chosen j step) d
        (RootIndexed.iteratedSelectedSubtreeStepField chosen j step)
        (back q).1 (back q).2) ≤
      φ (RootIndexed.position initial d step q.1 q.2)
    rw [hposition]
    change φ (RootIndexed.position initial d step
        (address (back q)).1 (address (back q)).2) ≤
      φ (RootIndexed.position initial d step q.1 q.2)
    rw [hback hq]

/-- Compose the inverse original-address embedding with any coupling out of
the iterated population. -/
noncomputable def RootIndexed.iteratedOriginalInjection.trans
    {Root α Mark Position Value : Type*}
    [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (initial : Root → Position)
    (d : Mark → Position)
    (chosen : ℕ → RootIndexed.StepField Root α Mark →
      Root → Root × TreeNode α)
    (j : ℕ) (step : RootIndexed.StepField Root α Mark)
    (hinj : Function.Injective
      (RootIndexed.iteratedSelectedAddress chosen j step))
    (population : Finset (RootIndexed.TreeNode Root α))
    (target : Cloud Unit Root α Position)
    (coupling : Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField
          (RootIndexed.iteratedSelectedInitialPosition
            initial d chosen j step)
          (RootIndexed.iteratedSelectedSubtreeStepField chosen j step))
        population) target ()) :
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial step)
        (RootIndexed.iteratedSelectedPopulation
          chosen j step hinj population))
      target () :=
  (RootIndexed.iteratedOriginalInjection φ initial d chosen j step hinj
    population).trans coupling

end ProbabilityTheory.BranchingRandomWalk

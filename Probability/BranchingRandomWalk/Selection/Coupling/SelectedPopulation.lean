import Probability.BranchingRandomWalk.Selection.Coupling.Generation
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Coupling to a causal root-indexed selected population

This instantiates the abstract all-generation offspring coupling with the
selected population constructed directly from a pre-sampled step field.
Offspring sets may be infinite.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

open Combinatorics.UlamHarris
open Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling
open Combinatorics.Branching.Selection.NSelection

variable {Root α Mark Position Value : Type*}

/-- An arbitrary capacity-bounded source process is dominated at every
generation by the causal first-`N` population formed from all surviving
offspring of a root-indexed pre-sampled field. -/
theorem injectivelyDominatesBy_selectedPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (φ : Position → Value) (d : Mark → Position) (N : ℕ)
    (roots : Finset Root) (initial : Root → Position)
    (sourceWalk : RootIndexed.StepField Root α Mark →
      RootIndexed.BranchingWalk Root α Mark Position)
    (sourcePopulation : ℕ → RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (sourceSlots : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Set α)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (n + 1) ω)
        (RootIndexed.childrenAtGeneration n parents ω))
    (hinitial : ∀ ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation 0 ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits 0 ω))
        PUnit.unit)
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      offspringAddressSet (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceCard : ∀ n ω, (sourcePopulation (n + 1) ω).card ≤ N)
    (hslots : ∀ n ω p, p ∈ sourcePopulation n ω →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      sourceSlots n ω p ⊆ {i | survive (ω q.1 q.2) i})
    (hsharedIncrement : ∀ n ω p, p ∈ sourcePopulation n ω →
      ∀ q, q ∈ RootIndexed.selectedPopulation
        N roots initial d φ hadmits n ω →
      φ ((RootIndexed.BranchingWalk.ofStepField initial ω).position d q.1 q.2) ≤
          φ ((sourceWalk ω).position d p.1 p.2) →
      ∀ i ∈ sourceSlots n ω p,
        value' ((ω q.1 q.2).map d) i =
          value' (((sourceWalk ω).step p.1 p.2).map d) i)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z)) :
    ∀ n ω,
      (populationCloud d (sourceWalk ω) (sourcePopulation n ω)).InjectivelyDominatesBy φ
        (populationCloud d
          (RootIndexed.BranchingWalk.ofStepField initial ω)
          (RootIndexed.selectedPopulation N roots initial d φ hadmits n ω))
        PUnit.unit := by
  apply injectivelyDominatesBy_all_generations_of_isFirstNBy
    φ d N sourceWalk
    (fun ω => RootIndexed.BranchingWalk.ofStepField initial ω)
    sourcePopulation
    (RootIndexed.selectedPopulation N roots initial d φ hadmits)
    sourceSlots
    (fun _ ω p => {i | survive (ω p.1 p.2) i})
    hinitial hsourceSubset hsourceCard
  · exact fun n ω => RootIndexed.selectedPopulation_succ_spec_position
      N roots initial d φ hadmits n ω
  · exact hslots
  · exact hsharedIncrement
  · exact htranslate

end ProbabilityTheory.BranchingRandomWalk.Selection.Coupling

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Iteration
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coupling

/-!
# Spatial realization of an iterated split pool

Finite populations in the iterated active/reserve field are embedded into
the original pre-sampled field through the cumulative split-pool address map.
Their absolute positions agree exactly.
-/

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling

/-- Original pre-sampled addresses occupied by a finite population in an
iterated split pool. -/
noncomputable def originalPopulation
    {Reserve α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Fin N ⊕ Reserve)
    (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X)
    (population : Finset
      (RootIndexed.TreeNode (Fin N ⊕ Reserve) α)) :
    Finset (RootIndexed.TreeNode (Fin N ⊕ Reserve) α) :=
  RootIndexed.iteratedSelectedPopulation
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step
    (iteratedPoolAddress_injective N R trial duration target fallback
      hfallbackDepth hfallbackInjective reserve hreserve htrial
      hfallbackReserve stem hstem j step)
    population

/-- A population in the iterated split pool and its original-address image
have equal positions, expressed as mutual spatial coupling in the direction
used by the selection machinery. -/
theorem iteratedPopulation_injectivelyDominatesBy_original
    {Reserve α Mark Position Value : Type*}
    [LinearOrder (TreeNode α)] [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (reserve : Reserve → Fin N ⊕ Reserve)
    (hreserve : Function.Injective reserve)
    (htrial : ∀ k r, trial k ≠ reserve r)
    (hfallbackReserve : ∀ i r, (fallback i).1 ≠ reserve r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (initial : Fin N ⊕ Reserve → Position)
    (j : ℕ)
    (step : RootIndexed.StepField (Fin N ⊕ Reserve) α Mark)
    (population : Finset
      (RootIndexed.TreeNode (Fin N ⊕ Reserve) α)) :
    (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField
          (iteratedPoolInitialPosition N R initial d trial duration target
            fallback reserve stem j step)
          (iteratedPoolField N R trial duration target fallback reserve stem
            j step))
        population).InjectivelyDominatesBy φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial step)
        (originalPopulation N R trial duration target fallback
          hfallbackDepth hfallbackInjective reserve hreserve htrial
          hfallbackReserve stem hstem j step population)) () := by
  exact RootIndexed.iteratedPopulation_injectivelyDominatesBy_original
    φ initial d
    (fun _ => poolRoots N R trial duration target fallback reserve stem)
    j step
    (iteratedPoolAddress_injective N R trial duration target fallback
      hfallbackDepth hfallbackInjective reserve hreserve htrial
      hfallbackReserve stem hstem j step)
    population

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

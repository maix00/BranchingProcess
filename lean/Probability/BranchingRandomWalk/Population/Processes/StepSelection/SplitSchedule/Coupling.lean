import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Iteration
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coupling
import Probability.BranchingRandomWalk.Selection.Coupling.StepSelection

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

/-- Descendants selected from every active root of an iterated split pool. -/
noncomputable def activePopulation
    {Reserve α X : Type*} (N : ℕ) [LinearOrder (TreeNode α)]
    [DecidableEq (RootIndexed.TreeNode (Fin N ⊕ Reserve) α)]
    (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (j n : ℕ) (step : RootIndexed.StepField (Fin N ⊕ Reserve) α X) :
    Finset (RootIndexed.TreeNode (Fin N ⊕ Reserve) α) :=
  RootIndexed.StepSelection.labelledPopulationOn R (activeRoots N) n
    (iteratedPoolField N R trial duration target fallback reserve stem j step)

/-- Couple the finite active population of any iterated split pool to a
causal first-`N` target by recursively installing equal-rank source steps.
The base field and fallback target may be random, and the absolute initial
positions may consequently depend on the same sample. -/
noncomputable def coupledInjection
    {Ω Reserve α Mark Position Value : Type*}
    (N : ℕ)
    [LinearOrder (TreeNode α)]
    [LinearOrder (RootIndexed.TreeNode (Fin N ⊕ Reserve) α)]
    [LinearOrder Value] [AddCommMonoid Position]
    (R : Step.FiniteSelection α Mark)
    (trial : ℕ → Fin N ⊕ Reserve) (duration target : ℕ)
    (restartFallback : Fin N → (Fin N ⊕ Reserve) × TreeNode α)
    (reserve : Reserve → Fin N ⊕ Reserve) (stem : TreeNode α)
    (base fallback : Ω → RootIndexed.StepField (Fin N ⊕ Reserve) α Mark)
    (initial : Fin N ⊕ Reserve → Position)
    (d : Mark → Position) (φ : Position → Value)
    (j : ℕ)
    (hadmits : ∀ (ω : Ω) (n : ℕ)
        (β : RootIndexed.StepField (Fin N ⊕ Reserve) α Mark)
        (parents : Finset
          (RootIndexed.TreeNode (Fin N ⊕ Reserve) α)),
      Combinatorics.Branching.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration
          (iteratedPoolInitialPosition N R initial d trial duration target
            restartFallback reserve stem j (base ω))
          d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (hcard : ∀ n ω,
      (activePopulation N R trial duration target restartFallback reserve stem
        j n (base ω)).card ≤ N)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    let sourceStep := fun sample =>
      iteratedPoolField N R trial duration target restartFallback reserve stem
        j (base sample)
    let initialAt := fun sample =>
      iteratedPoolInitialPosition N R initial d trial duration target
        restartFallback reserve stem j (base sample)
    let sourcePopulation := fun k sample =>
      activePopulation N R trial duration target restartFallback reserve stem
        j k (base sample)
    let targetStep := ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.coupledField
      N (activeRoots N) initialAt d φ hadmits
        sourceStep fallback sourcePopulation n ω
    let targetPopulation :=
      ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.coupledPopulation
        N (activeRoots N) initialAt d φ hadmits sourceStep
          fallback sourcePopulation n ω
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initialAt ω) (sourceStep ω))
        (sourcePopulation n ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initialAt ω) targetStep)
        targetPopulation) () := by
  dsimp only
  simpa [activePopulation] using
    (ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.RootIndexed.coupledInjection_labelledPopulationOn
      N R (activeRoots N) (activeRoots N) Finset.Subset.rfl
      (fun sample => iteratedPoolInitialPosition N R initial d trial duration
        target restartFallback reserve stem j (base sample))
      d φ hadmits
      (fun sample => iteratedPoolField N R trial duration target restartFallback
        reserve stem j (base sample))
      fallback
      (by simpa [activePopulation] using hcard)
      htranslate n ω)

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

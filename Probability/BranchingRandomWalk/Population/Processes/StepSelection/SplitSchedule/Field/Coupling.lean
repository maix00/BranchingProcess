/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Field.Iteration
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Coupling
import Probability.BranchingRandomWalk.Selection.Coupling.StepSelection

/-!
# Spatial realization of an iterated split pool

Finite populations in the iterated active and additional-root field are embedded into
the original pre-sampled field through the cumulative split-pool address map.
Their absolute positions agree exactly.
## Public declarations

For every finite active population, the causal coupling embeds it into the
corresponding original-field population and preserves the potential values:

\[\operatorname{Cloud}_{\phi}(\operatorname{activePopulation}_j)
  \succeq_{\mathrm{inj},\phi}
  \operatorname{Cloud}_{\phi}(\operatorname{originalPopulation}_j),\qquad
  \operatorname{position}_{\mathrm{active}}(p)
   =\operatorname{position}_{\mathrm{original}}(\Phi_j(p)).\]

* `activePopulation` reads the active roots at restart stage `j`;
  `coupledInjection` maps that population into the corresponding original
  field population, while `originalPopulation` defines the original-address population.
* `iteratedPopulation_injectivelyDominatesBy_original` proves that the active
  population embeds injectively into the original population with matching
  spatial values under the potential map.
-/

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.Coupling

/-- Descendants selected from every active root of an iterated split pool. -/
noncomputable def activePopulation
    {AdditionalRoot α X : Type*} (N : ℕ) [LinearOrder (TreeNode α)]
    [DecidableEq (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α)]
    (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (j n : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X) :
    Finset (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α) :=
  RootIndexed.StepSelection.labelledPopulationOn R (activeRoots N) n
    (iteratedPoolField N R trial duration target fallback additionalRoots stem j step)

/-- Couple the finite active population of an iterated split pool to its
first-`N` BRW counterpart by recursively installing matched steps at equal rank.
The base field and fallback field may be random, and the absolute initial
positions may consequently depend on the same sample. -/
noncomputable def coupledInjection
    {Ω AdditionalRoot α Mark Position Value : Type*}
    (N : ℕ)
    [LinearOrder (TreeNode α)]
    [LinearOrder (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α)]
    [LinearOrder Value] [AddCommMonoid Position]
    (R : Step.FiniteSelection α Mark)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (restartFallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot) (stem : TreeNode α)
    (base fallback : Ω → RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α Mark)
    (initial : Fin N ⊕ AdditionalRoot → Position)
    (d : Mark → Position) (φ : Position → Value)
    (j : ℕ)
    (hadmits : ∀ (ω : Ω) (n : ℕ)
        (β : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α Mark)
        (parents : Finset
          (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α)),
      Combinatorics.Selection.NSelection.AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration
          (iteratedPoolInitialPosition N R initial d trial duration target
            restartFallback additionalRoots stem j (base ω))
          d φ (n + 1) β)
        (Combinatorics.Branching.Population.childrenAtGeneration n parents β))
    (hcard : ∀ n ω,
      (activePopulation N R trial duration target restartFallback additionalRoots stem
        j n (base ω)).card ≤ N)
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω) :
    let selectedBRWStepField := fun sample =>
      iteratedPoolField N R trial duration target restartFallback additionalRoots stem
        j (base sample)
    let initialAt := fun sample =>
      iteratedPoolInitialPosition N R initial d trial duration target
        restartFallback additionalRoots stem j (base sample)
    let selectedBRWPopulation := fun k sample =>
      activePopulation N R trial duration target restartFallback additionalRoots stem
        j k (base sample)
    let nSelectedBRWStepField := ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.coupledField
      N (activeRoots N) initialAt d φ hadmits
        selectedBRWStepField fallback selectedBRWPopulation n ω
    let nSelectedBRWPopulation :=
      ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.coupledPopulation
        N (activeRoots N) initialAt d φ hadmits selectedBRWStepField
          fallback selectedBRWPopulation n ω
    Cloud.SliceDominatingMap φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initialAt ω) (selectedBRWStepField ω))
        (selectedBRWPopulation n ω))
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initialAt ω) nSelectedBRWStepField)
        nSelectedBRWPopulation) () := by
  dsimp only
  simpa [activePopulation] using
    (ProbabilityTheory.BranchingRandomWalk.Selection.Coupling.RootIndexed.coupledInjection_labelledPopulation
      N R (activeRoots N) (activeRoots N) Finset.Subset.rfl
      (fun sample => iteratedPoolInitialPosition N R initial d trial duration
        target restartFallback additionalRoots stem j (base sample))
      d φ hadmits
      (fun sample => iteratedPoolField N R trial duration target restartFallback
        additionalRoots stem j (base sample))
      fallback
      (by simpa [activePopulation] using hcard)
      htranslate n ω)

/-- Original pre-sampled addresses occupied by a finite population in an
iterated split pool. -/
noncomputable def originalPopulation
    {AdditionalRoot α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot)
    (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (j : ℕ) (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α X)
    (population : Finset
      (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α)) :
    Finset (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α) :=
  RootIndexed.iteratedSelectedPopulation
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step
    (iteratedPoolAddress_injective N R trial duration target fallback
      hfallbackDepth hfallbackInjective additionalRoots hadditionalRoots htrial
      hfallbackAdditionalRoots stem hstem j step)
    population

/-- A population in the iterated split pool and its original-address image
have equal positions, expressed as mutual spatial coupling in the direction
used by the selection machinery. -/
theorem iteratedPopulation_injectivelyDominatesBy_original
    {AdditionalRoot α Mark Position Value : Type*}
    [LinearOrder (TreeNode α)] [AddCommMonoid Position] [Preorder Value]
    (φ : Position → Value) (d : Mark → Position)
    (N : ℕ) (R : Step.FiniteSelection α Mark)
    (trial : ℕ → Fin N ⊕ AdditionalRoot) (duration target : ℕ)
    (fallback : Fin N → (Fin N ⊕ AdditionalRoot) × TreeNode α)
    (hfallbackDepth : ∀ i, (fallback i).2.length = duration)
    (hfallbackInjective : Function.Injective fallback)
    (additionalRoots : AdditionalRoot → Fin N ⊕ AdditionalRoot)
    (hadditionalRoots : Function.Injective additionalRoots)
    (htrial : ∀ k r, trial k ≠ additionalRoots r)
    (hfallbackAdditionalRoots : ∀ i r, (fallback i).1 ≠ additionalRoots r)
    (stem : TreeNode α) (hstem : stem.length = duration)
    (initial : Fin N ⊕ AdditionalRoot → Position)
    (j : ℕ)
    (step : RootIndexed.StepField (Fin N ⊕ AdditionalRoot) α Mark)
    (population : Finset
      (RootIndexed.TreeNode (Fin N ⊕ AdditionalRoot) α)) :
    (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField
          (iteratedPoolInitialPosition N R initial d trial duration target
            fallback additionalRoots stem j step)
          (iteratedPoolField N R trial duration target fallback additionalRoots stem
            j step))
        population).InjectivelyDominatesBy φ
      (populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initial step)
        (originalPopulation N R trial duration target fallback
          hfallbackDepth hfallbackInjective additionalRoots hadditionalRoots htrial
          hfallbackAdditionalRoots stem hstem j step population)) () := by
  exact RootIndexed.iteratedPopulation_injectivelyDominatesBy_original
    φ initial d
    (fun _ => poolRoots N R trial duration target fallback additionalRoots stem)
    j step
    (iteratedPoolAddress_injective N R trial duration target fallback
      hfallbackDepth hfallbackInjective additionalRoots hadditionalRoots htrial
      hfallbackAdditionalRoots stem hstem j step)
    population

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk

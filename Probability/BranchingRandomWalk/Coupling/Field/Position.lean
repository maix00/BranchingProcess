/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Coupling.Field.Ranked
import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step

/-!
# A recursively matched field for the selected branching walk

This file specializes the abstract rank-installed field to spatial branching
walks.  Source and target ranks are computed from their path positions, while
the target population is the causal first-`N` population of the field built
so far.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection
open Combinatorics.Branching.Selection.NSelection

variable {Ω Root α Mark Position Value : Type*}

/-- The target field obtained by installing the source step of each particle
at the target particle of the same spatial rank, one generation at a time. -/
noncomputable def RootIndexed.coupledField
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α)) :
    ℕ → Ω → RootIndexed.StepField Root α Mark :=
  BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField
    (fun _ ω p => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) (sourceStep ω)).position d p.1 p.2))
    (fun _ ω β p => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) β).position d p.1 p.2))
    sourcePopulation
    (fun n ω β => RootIndexed.selectedPopulation
      N roots (initial ω) d φ (hadmits ω) n β)
    sourceStep fallback

/-- The target selected population at a finite recursive coupling stage. -/
noncomputable def RootIndexed.coupledPopulation
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) : Finset (RootIndexed.TreeNode Root α) :=
  RootIndexed.selectedPopulation N roots (initial ω) d φ (hadmits ω) n
    (RootIndexed.coupledField N roots initial d φ hadmits
      sourceStep fallback sourcePopulation n ω)

/-- Installing the current matched steps leaves the current target population
unchanged. -/
theorem RootIndexed.coupledPopulation_succ_stage
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) :
    RootIndexed.selectedPopulation N roots (initial ω) d φ (hadmits ω) n
        (RootIndexed.coupledField N roots initial d φ hadmits
          sourceStep fallback sourcePopulation (n + 1) ω) =
      RootIndexed.coupledPopulation N roots initial d φ hadmits
        sourceStep fallback sourcePopulation n ω := by
  exact BranchingRandomWalk.Coupling.RootIndexed.selectedPopulation_rankInstalledField_succ
    N roots (initial ω) d φ (hadmits ω) _ _ _ _ sourceStep fallback n ω

/-- The successor installation changes no spatial position through the parent
generation at which it is installed. -/
theorem RootIndexed.coupledField_position_succ_of_depth_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω) (q : RootIndexed.TreeNode Root α)
    (hq : q.2.length ≤ n) :
    (RootIndexed.BranchingWalk.ofStepField (initial ω)
      (RootIndexed.coupledField N roots initial d φ hadmits sourceStep fallback
        sourcePopulation (n + 1) ω)).position d q.1 q.2 =
      (RootIndexed.BranchingWalk.ofStepField (initial ω)
        (RootIndexed.coupledField N roots initial d φ hadmits sourceStep fallback
          sourcePopulation n ω)).position d q.1 q.2 := by
  rw [RootIndexed.coupledField,
    BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_succ]
  exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
    d n (initial ω) _ _ q.1 q.2 hq

/-- At the successor stage, the step at the target parent of equal spatial
rank is exactly the corresponding source step. -/
theorem RootIndexed.coupledField_succ_apply_matchByRankOrSelf
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (ω : Ω)
    (hcard : (sourcePopulation n ω).card ≤
      (RootIndexed.coupledPopulation N roots initial d φ hadmits
        sourceStep fallback sourcePopulation n ω).card)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ sourcePopulation n ω) :
    let sourceValue := fun q => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) (sourceStep ω)).position d q.1 q.2)
    let prior := RootIndexed.coupledField N roots initial d φ hadmits
      sourceStep fallback sourcePopulation n ω
    let targetValue := fun q => φ ((RootIndexed.BranchingWalk.ofStepField
      (initial ω) prior).position d q.1 q.2)
    let q := matchByRankOrSelf sourceValue targetValue
      (sourcePopulation n ω)
      (RootIndexed.coupledPopulation N roots initial d φ hadmits
        sourceStep fallback sourcePopulation n ω) hcard p
    RootIndexed.coupledField N roots initial d φ hadmits sourceStep fallback
        sourcePopulation (n + 1) ω q.1 q.2 =
      sourceStep ω p.1 p.2 := by
  dsimp only
  apply BranchingRandomWalk.Coupling.RootIndexed.rankInstalledField_succ_apply_matchByRankOrSelf
  · intro q hq
    exact RootIndexed.selectedPopulation_depth N roots (initial ω) d φ (hadmits ω)
      n (RootIndexed.coupledField N roots initial d φ hadmits
        sourceStep fallback sourcePopulation n ω) q hq
  · exact hp

/-- The recursive equal-rank installation realizes a pathwise coupling of an
arbitrary capacity-bounded source population with the causal first-`N` target
population.  Child-slot sets remain arbitrary sets; no countability of roots
or slots is used. -/
noncomputable def RootIndexed.coupledInjection
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Ω → Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (ω : Ω) (n : ℕ) (β : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration (initial ω) d φ (n + 1) β)
        (RootIndexed.childrenAtGeneration n parents β))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α Mark)
    (sourcePopulation : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceSlots : ℕ → Ω → RootIndexed.TreeNode Root α → Set α)
    (initialInjection : ∀ ω, Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (sourceStep ω))
        (sourcePopulation 0 ω))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (fallback ω))
        (RootIndexed.coupledPopulation N roots initial d φ hadmits sourceStep
          fallback sourcePopulation 0 ω)) ())
    (hsourceSubset : ∀ n ω, ↑(sourcePopulation (n + 1) ω) ⊆
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑(sourcePopulation n ω)) (sourceSlots n ω))
    (hsourceSlots : ∀ n ω p, p ∈ sourcePopulation n ω →
      sourceSlots n ω p ⊆ {i | survive (sourceStep ω p.1 p.2) i})
    (htranslate : ∀ x y z : Position,
      φ y ≤ φ x → φ (y + z) ≤ φ (x + z))
    (n : ℕ) (ω : Ω)
    (hsourceCard : ∀ k < n, (sourcePopulation (k + 1) ω).card ≤ N) :
    Cloud.SliceDominatingMap φ
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω) (sourceStep ω))
        (sourcePopulation n ω))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField (initial ω)
          (RootIndexed.coupledField N roots initial d φ hadmits sourceStep
            fallback sourcePopulation n ω))
        (RootIndexed.coupledPopulation N roots initial d φ hadmits sourceStep
          fallback sourcePopulation n ω)) () := by
  induction n with
  | zero =>
      simpa [RootIndexed.coupledField] using initialInjection ω
  | succ n ih =>
      have ih := ih (fun k hk => hsourceCard k (Nat.lt_succ_of_lt hk))
      let sourceWalk := RootIndexed.BranchingWalk.ofStepField (initial ω)
        (sourceStep ω)
      let priorField := RootIndexed.coupledField N roots initial d φ hadmits
        sourceStep fallback sourcePopulation n ω
      let nextField := RootIndexed.coupledField N roots initial d φ hadmits
        sourceStep fallback sourcePopulation (n + 1) ω
      let targetParents := RootIndexed.coupledPopulation N roots initial d φ
        hadmits sourceStep fallback sourcePopulation n ω
      let canonical := Combinatorics.Branching.Selection.Coupling.canonicalInjection
        φ d sourceWalk (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
        (sourcePopulation n ω) targetParents ih
      let hparents : Cloud.SliceDominatingMap φ
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            sourceWalk (sourcePopulation n ω))
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            (RootIndexed.BranchingWalk.ofStepField (initial ω) nextField)
            targetParents) () := {
        toFun := canonical
        mapsTo := canonical.mapsTo
        injOn := canonical.injOn
        dominates := by
          intro p hp
          change φ ((RootIndexed.BranchingWalk.ofStepField (initial ω) nextField).position
              d (canonical p).1 (canonical p).2) ≤
            φ (sourceWalk.position d p.1 p.2)
          rw [RootIndexed.coupledField_position_succ_of_depth_le N roots initial
            d φ hadmits sourceStep fallback sourcePopulation n ω (canonical p)]
          · exact canonical.dominates p hp
          · apply Nat.le_of_eq
            apply RootIndexed.selectedPopulation_depth N roots (initial ω) d φ (hadmits ω)
              n priorField (canonical p)
            simpa [targetParents, RootIndexed.coupledPopulation,
              Combinatorics.Branching.Selection.Coupling.populationCloud]
              using canonical.mapsTo hp }
      have hparents_apply (p : RootIndexed.TreeNode Root α) :
          hparents p = canonical p := rfl
      refine Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
          φ d N sourceWalk
          (RootIndexed.BranchingWalk.ofStepField (initial ω) nextField)
          (sourcePopulation n ω) targetParents
          (sourceSlots n ω)
          (fun q => {i | survive (nextField q.1 q.2) i})
          (sourcePopulation (n + 1) ω)
          (RootIndexed.coupledPopulation N roots initial d φ hadmits sourceStep
            fallback sourcePopulation (n + 1) ω)
          (hsourceSubset n ω) (hsourceCard n (Nat.lt_succ_self n))
          ?_ hparents ?_ ?_ htranslate
      · simpa [RootIndexed.coupledPopulation, targetParents, nextField,
          RootIndexed.coupledPopulation_succ_stage
          N roots initial d φ hadmits sourceStep fallback sourcePopulation n ω]
          using RootIndexed.selectedPopulation_succ_spec_position N roots (initial ω)
            d φ (hadmits ω) n nextField
      · intro p hp i hi
        have his := hsourceSlots n ω p
          (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
            using hp) hi
        have hstep : nextField (canonical p).1 (canonical p).2 =
            sourceStep ω p.1 p.2 := by
          change RootIndexed.coupledField N roots initial d φ hadmits sourceStep
            fallback sourcePopulation (n + 1) ω
              (canonical p).1 (canonical p).2 = sourceStep ω p.1 p.2
          rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
          exact RootIndexed.coupledField_succ_apply_matchByRankOrSelf N roots
            initial d φ hadmits sourceStep fallback sourcePopulation n ω
            (Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
                φ d sourceWalk
                (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
                (sourcePopulation n ω) targetParents ih)
            (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
              using hp)
        have hstep' : nextField (hparents p).1 (hparents p).2 =
            sourceStep ω p.1 p.2 := by simpa [hparents_apply] using hstep
        simpa [hstep'] using his
      · intro p hp i hi
        have hstep : nextField (canonical p).1 (canonical p).2 =
            sourceStep ω p.1 p.2 := by
          change RootIndexed.coupledField N roots initial d φ hadmits sourceStep
              fallback sourcePopulation (n + 1) ω
                (canonical p).1 (canonical p).2 = sourceStep ω p.1 p.2
          rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
          exact RootIndexed.coupledField_succ_apply_matchByRankOrSelf N roots
            initial d φ hadmits sourceStep fallback sourcePopulation n ω
            (Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
                φ d sourceWalk
                (RootIndexed.BranchingWalk.ofStepField (initial ω) priorField)
                (sourcePopulation n ω) targetParents ih)
            (by simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
              using hp)
        have hstep' : nextField (hparents p).1 (hparents p).2 =
            sourceStep ω p.1 p.2 := by simpa [hparents_apply] using hstep
        simp [sourceWalk, hstep']

end ProbabilityTheory.BranchingRandomWalk.Coupling

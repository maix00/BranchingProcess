/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed
import Probability.BranchingRandomWalk.Population.Candidates.GenerationUpdate

/-!
# Selected populations under generation-local field updates

Installing steps at generation `m` leaves every selected population through
that generation unchanged.  The proof uses only the intrinsic `IsFirstNBy`
specification, so it does not depend on how the finite initial segment is
constructed or on countability of the ambient particle type.
-/

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

noncomputable section

variable {Root α Mark Position Value : Type*}

/-- Updating the steps owned by generation `m` cannot change selected
populations at generations `n ≤ m`. -/
theorem selectedPopulation_updateGeneration_of_le
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n m : ℕ) (hnm : n ≤ m)
    (replacement fallback : RootIndexed.StepField Root α Mark) :
    selectedPopulation N roots initial d φ hadmits n
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          m replacement fallback) =
      selectedPopulation N roots initial d φ hadmits n fallback := by
  let updated :=
    Combinatorics.Branching.RootIndexed.StepField.updateGeneration
      m replacement fallback
  induction n with
  | zero => rfl
  | succ k ih =>
      have hklt : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) hnm
      have hparents :
          selectedPopulation N roots initial d φ hadmits k updated =
            selectedPopulation N roots initial d φ hadmits k fallback :=
        ih (Nat.le_of_succ_le hnm)
      let parents := selectedPopulation N roots initial d φ hadmits k fallback
      have hcandidates :
          childrenAtGeneration k parents updated =
            childrenAtGeneration k parents fallback := by
        exact childrenAtGeneration_updateGeneration_of_lt
          k m hklt parents replacement fallback
      have hvalue : Set.EqOn
          (observedPositionAtGeneration initial d φ (k + 1) fallback)
          (observedPositionAtGeneration initial d φ (k + 1) updated)
          (childrenAtGeneration k parents fallback) := by
        intro q hq
        have hdepth : q.2.length = k + 1 :=
          childrenAtGeneration_depth k parents fallback q hq
        rw [observedPositionAtGeneration_eq initial d φ (k + 1)
          fallback q hdepth]
        rw [observedPositionAtGeneration_eq initial d φ (k + 1)
          updated q hdepth]
        apply congrArg φ
        symm
        exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
          d m initial replacement fallback q.1 q.2 (by omega)
      have hupdated := selectedPopulation_succ_spec
        N roots initial d φ hadmits k updated
      have hfallback := selectedPopulation_succ_spec
        N roots initial d φ hadmits k fallback
      rw [hparents] at hupdated
      have hfallback' := hfallback.congr_value hvalue
      rw [← hcandidates] at hfallback'
      exact hupdated.unique hfallback'

/-- In particular, installing a new step family at the currently selected
parent generation preserves that parent population exactly. -/
theorem selectedPopulation_updateGeneration
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : Mark → Position) (φ : Position → Value)
    (hadmits : ∀ (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ (n + 1) ω)
        (childrenAtGeneration n parents ω))
    (n : ℕ) (replacement fallback : RootIndexed.StepField Root α Mark) :
    selectedPopulation N roots initial d φ hadmits n
        (Combinatorics.Branching.RootIndexed.StepField.updateGeneration
          n replacement fallback) =
      selectedPopulation N roots initial d φ hadmits n fallback :=
  selectedPopulation_updateGeneration_of_le N roots initial d φ hadmits
    n n le_rfl replacement fallback

end

end ProbabilityTheory.BranchingRandomWalk.RootIndexed

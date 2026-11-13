/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import all Probability.BranchingRandomWalk.Coupling.Rank.Block.Lemmas.Glue

/-!
# Internal recursive-step identity

This identity expands one successor of the rank-installed field into the
coordinate gluing used by the past-measurability and product-law arguments.
It is specific to this recursive construction and remains in its internal
`Lemmas/` layer.

With `F_n` denoting `rankInstalledField` and `B_n` denoting
`rankInstalledBlockChoice`, it states

\[
  F_{n+1}(\omega)
  = \operatorname{glue}_n\bigl(F_n(\omega)_{<n},
      \operatorname{selectedCoordinates}(B_n,\omega)\bigr).
\]

## Internal proof declarations

- `RootIndexed.rankInstalledField_succ_eq_glue` is the displayed one-step
  identity, used by the past-measurability and product-law proofs.
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- One recursive successor stage is the predictable coordinate gluing used
by the product-law theorem. -/
lemma RootIndexed.rankInstalledField_succ_eq_glue
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) field =
      let prior := RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n field
      RootIndexed.StepField.glue n (prior.past n)
        (RootIndexed.selectedCoordinateField
          (RootIndexed.rankInstalledBlockChoice selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation n)
          field) := by
  let prior := RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
    RootIndexed.StepField.left RootIndexed.StepField.right n field
  rw [RootIndexed.rankInstalledField_succ]
  symm
  apply RootIndexed.glue_rankBlockChoice_eq_updateGeneration
  intro r u hu
  exact RootIndexed.rankInstalledField_apply_of_le_length selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey
    selectedBRWPopulation nSelectedBRWPopulation RootIndexed.StepField.left RootIndexed.StepField.right
    n field r u hu


end ProbabilityTheory.BranchingRandomWalk.Coupling

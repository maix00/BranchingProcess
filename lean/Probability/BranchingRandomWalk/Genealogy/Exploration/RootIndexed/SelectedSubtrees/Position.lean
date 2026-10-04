/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Positions

/-!
# Positions in selected subtree fields

The position space and edge-mark space remain separate.  Giving every
selected subtree its absolute position at the selected root makes all local
positions agree exactly with the corresponding positions in the original
root-indexed field.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Absolute initial positions for a fixed family of selected subtree roots. -/
def RootIndexed.subtreeInitialPosition
    {Root κ α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (step : RootIndexed.StepField Root α Mark)
    (roots : κ → Root × TreeNode α) : κ → Position :=
  fun i => RootIndexed.position initial d step (roots i).1 (roots i).2

/-- Rebasing a field at selected roots and rebasing its initial positions
preserves every absolute descendant position. -/
theorem RootIndexed.position_subtreeStepFieldVector
    {Root κ α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (step : RootIndexed.StepField Root α Mark)
    (roots : κ → Root × TreeNode α) (i : κ) (v : TreeNode α) :
    RootIndexed.position
        (RootIndexed.subtreeInitialPosition initial d step roots) d
        (RootIndexed.subtreeStepFieldVector roots step) i v =
      RootIndexed.position initial d step
        (roots i).1 ((roots i).2 ++ v) := by
  rw [RootIndexed.position_append]
  rfl

/-- Absolute initial positions for a family selected from the field itself. -/
def RootIndexed.selectedSubtreeInitialPosition
    {Root κ α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (chosen : RootIndexed.StepField Root α Mark →
      κ → Root × TreeNode α)
    (step : RootIndexed.StepField Root α Mark) : κ → Position :=
  RootIndexed.subtreeInitialPosition initial d step (chosen step)

theorem RootIndexed.position_selectedSubtreeStepFieldVector
    {Root κ α Mark Position : Type*} [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (chosen : RootIndexed.StepField Root α Mark →
      κ → Root × TreeNode α)
    (step : RootIndexed.StepField Root α Mark) (i : κ)
    (v : TreeNode α) :
    RootIndexed.position
        (RootIndexed.selectedSubtreeInitialPosition initial d chosen step) d
        (RootIndexed.selectedSubtreeStepFieldVector chosen step) i v =
      RootIndexed.position initial d step
        (chosen step i).1 ((chosen step i).2 ++ v) :=
  RootIndexed.position_subtreeStepFieldVector
    initial d step (chosen step) i v

end ProbabilityTheory.BranchingRandomWalk

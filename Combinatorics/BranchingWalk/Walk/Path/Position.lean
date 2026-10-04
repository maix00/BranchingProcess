/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Cloud
public import Combinatorics.BranchingWalk.Walk.Path.Block.Basic

/-!
# Walk paths as branching-walk displacements

This file identifies the linear path operations with the corresponding
displacement, position, and cloud operations of a singleton-slot branching
walk.
-/

@[expose] public section

namespace Combinatorics.Branching.Walk

open Combinatorics.UlamHarris

variable {Mark Position : Type*} [AddCommMonoid Position]

/-- Displacement along the unique lineage is the partial sum of the mapped
increments. -/
theorem displaceWith_lineNode_eq_partialSum (d : Mark → Position)
    (increment : ℕ → Mark) (n : ℕ) :
    displaceWith d (stepFieldOfIncrements increment) [] (lineNode n) =
      partialSum n (d ∘ increment) := by
  simpa [partialSum, Function.comp_apply] using
    displaceWith_lineNode d increment n

/-- Position along the unique lineage is the path history at the same time. -/
theorem position_lineNode_eq_history (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (n : ℕ) :
    (ofIncrements initial increment).position d PUnit.unit (lineNode n) =
      history n initial (d ∘ increment)
        ⟨n, Nat.lt_succ_self n⟩ := by
  rw [position_lineNode, history_last]
  rfl

/-- The standard time-indexed position process is exactly the position of the
unique lineage in the singleton-slot branching walk. -/
theorem position_lineNode_eq_positionProcess (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (n : ℕ) :
    (ofIncrements initial increment).position d PUnit.unit (lineNode n) =
      positionProcess initial n (d ∘ increment) := by
  rw [position_lineNode]
  rfl

/-- Moving forward by a block of generations adds precisely that block's
mapped increments. -/
theorem position_lineNode_add (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (start length : ℕ) :
    (ofIncrements initial increment).position d PUnit.unit
        (lineNode (start + length)) =
      (ofIncrements initial increment).position d PUnit.unit
          (lineNode start) +
        blockSum start length (d ∘ increment) := by
  rw [position_lineNode, position_lineNode, blockSum_eq_partialSum_natAdd,
    show (∑ k ∈ Finset.range (start + length), d (increment k)) =
      partialSum (start + length) (d ∘ increment) by rfl,
    show (∑ k ∈ Finset.range start, d (increment k)) =
      partialSum start (d ∘ increment) by rfl,
    partialSum_add]
  rw [add_assoc]

/-- The position stored by the generation cloud of a walk is its path
history. -/
theorem discreteTimeCloud_position_lineNode (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (n : ℕ) :
    (Cloud.discreteTimeCloud_ofBranchingWalk d
        (ofIncrements initial increment)).position PUnit.unit (lineNode n) =
      history n initial (d ∘ increment)
        ⟨n, Nat.lt_succ_self n⟩ := by
  exact position_lineNode_eq_history d initial increment n

/-- The generation cloud reads the same standard time-indexed position
process as the unique branching-walk lineage. -/
theorem discreteTimeCloud_position_lineNode_eq_positionProcess
    (d : Mark → Position) (initial : Position) (increment : ℕ → Mark)
    (n : ℕ) :
    (Cloud.discreteTimeCloud_ofBranchingWalk d
        (ofIncrements initial increment)).position PUnit.unit (lineNode n) =
      positionProcess initial n (d ∘ increment) := by
  exact position_lineNode_eq_positionProcess d initial increment n

/-- The unique lineage is present in the generation cloud produced from an
everywhere-present increment path. -/
theorem lineNode_mem_discreteTimeCloud (d : Mark → Position)
    (initial : Position) (increment : ℕ → Mark) (n : ℕ) :
    ((PUnit.unit, lineNode n) : RootIndexed.TreeNode PUnit PUnit) ∈
      (Cloud.discreteTimeCloud_ofBranchingWalk d
        (ofIncrements initial increment)).particles n := by
  simp [Cloud.discreteTimeCloud_ofBranchingWalk, Cloud.ofBranchingWalk,
    generation]
  exact surviveAlong_stepFieldOfIncrements increment [] (lineNode n)

end Combinatorics.Branching.Walk

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Population.Candidates.Generation
public import Combinatorics.BranchingWalk.Step.Measure.LeftLocalFiniteness

/-!
# Left local finiteness of generation candidates

## Public declarations

- \`childrenAtGeneration_isLowerFiniteBy_of_leftLocallyFinite\` proves that the
  union of a finite set of parents' shifted offspring configurations has finite
  lower position sections if each offspring configuration does.
-/

@[expose] public section

namespace Combinatorics.Branching.Population

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

theorem childrenAtGeneration_isLowerFiniteBy_of_leftLocallyFinite
    {Root α : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (field : Root → Combinatorics.Branching.StepField α ℝ)
    (initial : Root → ℝ)
    (hfinite : ∀ p ∈ parents, (field p.1 p.2).IsLeftLocallyFinite) :
    IsLowerFiniteBy
      (fun p =>
        (RootIndexed.BranchingWalk.ofStepField initial field).position
          id p.1 p.2)
      (childrenAtGeneration n parents field) := by
  let β := RootIndexed.BranchingWalk.ofStepField initial field
  let value : RootIndexed.TreeNode Root α → ℝ := fun q =>
    β.position id q.1 q.2
  change IsLowerFiniteBy value (childrenAtGeneration n parents field)
  apply childrenAtGeneration_isLowerFiniteBy n parents field value
  intro p hp a
  let ξ := field p.1 p.2
  apply (hfinite p hp (a - value p)).subset
  intro i hi
  refine ⟨hi.1, ?_⟩
  have hchildpos : value (RootIndexed.childAddress p i) =
      value p + value' (ξ.map id) i := by
    simpa [value, β, RootIndexed.childAddress] using
      (Combinatorics.Branching.RootIndexed.BranchingWalk.position_child id
        (RootIndexed.BranchingWalk.ofStepField initial field) p.1 p.2 i)
  exact (le_sub_iff_add_le).2 (by
    simpa [add_comm, hchildpos] using hi.2)

end Combinatorics.Branching.Population

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Population.Candidates.Generation
public import Combinatorics.BranchingWalk.Step.Measure.ExponentialWeight

/-!
# Lower-finite offspring populations from exponential weights

## Public declarations

- `Combinatorics.Branching.Population.childrenAtGeneration_isLowerFiniteBy_real`
  states that if every parent in a finite parent set has
  finite total negative exponential offspring weight, then the real-position
  order on its generation-$(n+1)$ child set has finite lower sections. Thus
  this child set admits selection of its first $N$ elements for every finite
  capacity $N$.

-/

@[expose] public section

namespace Combinatorics.Branching.Population

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

theorem childrenAtGeneration_isLowerFiniteBy_real
    {Root α : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (field : Root → Combinatorics.Branching.StepField α ℝ)
    (initial : Root → ℝ)
    (hweight : ∀ p ∈ parents,
      Combinatorics.Branching.totalPotentialWeight
        Combinatorics.Branching.realPotential (-1) (field p.1 p.2) ≠ ∞) :
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
  have hfinite := Combinatorics.Branching.finite_realized_children_potential_below
    Combinatorics.Branching.realPotential ξ (hweight p hp)
      (a - value p)
  apply hfinite.subset
  intro i hi
  refine ⟨hi.1, ?_⟩
  have hchildpos : value (RootIndexed.childAddress p i) =
      value p + value' (ξ.map id) i := by
    simpa [value, β, RootIndexed.childAddress] using
      (Combinatorics.Branching.RootIndexed.BranchingWalk.position_child id
        (RootIndexed.BranchingWalk.ofStepField initial field) p.1 p.2 i)
  have hpotential : ξ.potentialValue' Combinatorics.Branching.realPotential i =
      value' (ξ.map id) i := by
    cases hslot : ξ i <;>
      simp [Step.map, value', Step.potentialValue', Step.potentialAt?,
        Combinatorics.Branching.realPotential, ξ, hslot]
  rw [hpotential]
  exact (le_sub_iff_add_le).2 (by
    simpa [add_comm, hchildpos] using hi.2)

end Combinatorics.Branching.Population

end

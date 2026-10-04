/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed
public import Probability.BranchingRandomWalk.Selection.NSelection.Position
public import Combinatorics.BranchingWalk.Step.ExponentialWeight

/-!
# Real-position admissibility from exponential offspring weight

Finite negative exponential offspring weight gives finite displacement
sublevel sets.  Additivity of real positions transfers this local property
to the full child population of any finite generation slice.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open scoped ENNReal

theorem childrenAtGeneration_isLowerFiniteBy_real
    {Root α : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField Root α ℝ)
    (initial : Root → ℝ)
    (hparents : ∀ p ∈ parents, p.2.length = n)
    (hweight : ∀ p ∈ parents,
      totalPotentialWeight realPotential (-1) (field p.1 p.2) ≠ ∞) :
    IsLowerFiniteBy
      (RootIndexed.observedPositionAtGeneration initial id id (n + 1) field)
      (childrenAtGeneration n parents field) := by
  apply childrenAtGeneration_isLowerFiniteBy
  intro p hp a
  let ξ := field p.1 p.2
  let value := RootIndexed.observedPositionAtGeneration initial id id
    (n + 1) field
  let parentValue := RootIndexed.observedPositionAtGeneration initial id id n field
  have hfinite := finite_realized_children_potential_below
    realPotential ξ (hweight p hp) (a - parentValue p)
  apply hfinite.subset
  intro i hi
  refine ⟨hi.1, ?_⟩
  have hchildpos : value (p.1, p.2 ++ [i]) =
      parentValue p + value' (ξ.map id) i := by
    unfold value parentValue
    rw [RootIndexed.observedPositionAtGeneration_eq initial id id
      (n + 1) field (p.1, p.2 ++ [i]) (by simp [hparents p hp])]
    rw [RootIndexed.observedPositionAtGeneration_eq initial id id
      n field p (hparents p hp)]
    simpa [value, parentValue, ξ] using
      (Combinatorics.Branching.RootIndexed.BranchingWalk.position_child id
        (Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField
          initial field) p.1 p.2 i)
  have hpotential : ξ.potentialValue' realPotential i =
      value' (ξ.map id) i := by
    cases hslot : ξ i <;>
      simp [Step.map, value', Step.potentialValue', Step.potentialAt?,
        realPotential, ξ, hslot]
  have hsum : parentValue p + value' (ξ.map id) i ≤ a := by
    rw [← hchildpos]
    exact hi.2
  rw [hpotential]
  rw [le_sub_iff_add_le]
  linarith

end ProbabilityTheory.BranchingRandomWalk.RootIndexed

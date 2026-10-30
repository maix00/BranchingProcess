/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Candidates.ExponentialWeight
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability

/-!
# Lower-finite child positions in a root-indexed step field

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.childrenAtGeneration_isLowerFiniteBy_real`
  states that finite negative exponential offspring weight at every parent
  makes the generation-truncated real-position order on the next generation's
  child set lower finite. It specializes the deterministic branching-walk
  position theorem to the field observable used by the N-selection process.

-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

theorem childrenAtGeneration_isLowerFiniteBy_real
    {Root α : Type*} [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (n : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
    (field : StepField Root α ℝ) (initial : Root → ℝ)
    (hweight : ∀ p ∈ parents,
      Combinatorics.Branching.totalPotentialWeight
        Combinatorics.Branching.realPotential (-1) (field p.1 p.2) ≠ ∞) :
    IsLowerFiniteBy
      (observedPositionAtGeneration initial id id (n + 1) field)
      (Combinatorics.Branching.Population.childrenAtGeneration n parents field) := by
  let β := Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField
    initial field
  let value := fun p : RootIndexed.TreeNode Root α => β.position id p.1 p.2
  have hbase :=
    Combinatorics.Branching.Population.childrenAtGeneration_isLowerFiniteBy_real
      n parents field initial hweight
  have hobserved (q : RootIndexed.TreeNode Root α)
      (hq : q ∈ Combinatorics.Branching.Population.childrenAtGeneration
        n parents field) :
      observedPositionAtGeneration initial id id (n + 1) field q = value q := by
    rw [observedPositionAtGeneration_eq initial id id (n + 1) field q
      (Combinatorics.Branching.Population.childrenAtGeneration_depth
        n parents field q hq)]
    rfl
  intro p hp
  have hfinite := hbase p hp
  apply hfinite.subset
  intro q hq
  refine ⟨hq.1, ?_⟩
  change toLex (value q, q) ≤ toLex (value p, p)
  rw [← hobserved q hq.1, ← hobserved p hp]
  exact hq.2

end ProbabilityTheory.BranchingRandomWalk.RootIndexed

end

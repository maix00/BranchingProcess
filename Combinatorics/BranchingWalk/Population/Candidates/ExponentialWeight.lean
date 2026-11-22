/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Candidates.RealPosition

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
  apply childrenAtGeneration_isLowerFiniteBy_of_leftLocallyFinite
  intro p hp
  exact (field p.1 p.2).isLeftLocallyFinite_of_totalPotentialWeight_ne_top
    (β := 1) zero_lt_one (hweight p hp)

end Combinatorics.Branching.Population

end

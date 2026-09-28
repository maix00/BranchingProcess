import Combinatorics.BranchingWalk.Walk.Basic

/-!
# Survival of branching walks

Survival is a property of a branching walk, independent of positions.  A walk
survives to generation `n` when some realized address has length `n`; it
survives forever when this holds at every generation.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

namespace RootIndexed.BranchingWalk

/-- A specified root has a surviving descendant in generation `n`. -/
def SurvivesToGeneration {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) (n : ℕ) : Prop :=
  ∃ u : TreeNode α, u.length = n ∧ surviveAlong (walk.step root) [] u

/-- A specified root has a surviving descendant in every generation. -/
def SurvivesForever {Root α Mark Position : Type*}
    (walk : RootIndexed.BranchingWalk Root α Mark Position)
    (root : Root) : Prop :=
  ∀ n, walk.SurvivesToGeneration root n

end RootIndexed.BranchingWalk

namespace BranchingWalk

/-- Permanent survival for a single-root branching walk. -/
def SurvivesForever {α Mark Position : Type*}
    (walk : BranchingWalk α Mark Position) : Prop :=
  RootIndexed.BranchingWalk.SurvivesForever walk PUnit.unit

end BranchingWalk

namespace Walk

/-- An increment-path realization survives forever. -/
theorem ofIncrements_survivesForever {Mark Position : Type*}
    (initial : Position) (increment : ℕ → Mark) :
    (ofIncrements initial increment).SurvivesForever := by
  intro n
  exact ⟨lineNode n, lineNode_length n,
    surviveAlong_stepFieldOfIncrements increment _ _⟩

end Walk
end Combinatorics.Branching

import Combinatorics.BranchingWalk.Basic.Displace

/-!
# Positions

Absolute positions obtained by shifting path displacement by an initial
position. All position definitions for deterministic branching walks live in
the Cloud layer.
-/

namespace Combinatorics
namespace Branching

open Combinatorics.UlamHarris

/-- The absolute position of a node. -/
def position {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : StepField α X) (u : TreeNode α) : X :=
  initial + displaceRoot step u

/-- The absolute position of a node in a root-indexed walk. -/
def rootIndexedPosition {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → StepField α X)
    (r : Root) (u : TreeNode α) : X :=
  initial r + displaceRoot (step r) u

@[simp] theorem position_root {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : StepField α X) :
    position initial step [] = initial := by
  simp [position, displaceRoot]

@[simp] theorem rootIndexedPosition_root
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → StepField α X) (r : Root) :
    rootIndexedPosition initial step r [] = initial r := by
  simp [rootIndexedPosition, displaceRoot]

theorem rootIndexedPosition_eq_position
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → StepField α X)
    (r : Root) (u : TreeNode α) :
    rootIndexedPosition initial step r u =
      position (initial r) (step r) u := by
  rfl

end Branching
end Combinatorics

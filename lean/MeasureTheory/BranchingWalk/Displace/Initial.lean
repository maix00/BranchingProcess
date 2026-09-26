import MeasureTheory.BranchingWalk.Displace.Basic

/-!
# Initial-position-shifted node positions

`nodePosition initial step u` is the absolute position of the node `u` when
the walk starts at `initial`.  The displacement `displaceRoot step u` is the
increment from the root; the initial position is an independent geometric
datum and is therefore kept as an explicit argument.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- The absolute position of a node, obtained by shifting the root
displacement by the initial position. -/
def nodePosition {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : BranchingWalk α X) (u : TreeNode α) : X :=
  initial + displaceRoot step u

/-- The same position function for a root-indexed walk. -/
def rootIndexedNodePosition {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → BranchingWalk α X)
    (r : Root) (u : TreeNode α) : X :=
  initial r + displaceRoot (step r) u

@[simp] theorem nodePosition_root {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : BranchingWalk α X) :
    nodePosition initial step [] = initial := by
  simp [nodePosition, displaceRoot]

@[simp] theorem rootIndexedNodePosition_root
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → BranchingWalk α X) (r : Root) :
    rootIndexedNodePosition initial step r [] = initial r := by
  simp [rootIndexedNodePosition, displaceRoot]

theorem rootIndexedNodePosition_eq_nodePosition
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → BranchingWalk α X)
    (r : Root) (u : TreeNode α) :
    rootIndexedNodePosition initial step r u =
      nodePosition (initial r) (step r) u := by
  rfl

end BranchingWalk

end MeasureTheory

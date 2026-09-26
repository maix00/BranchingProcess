import Combinatorics.BranchingWalk.Displace.Initial

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Canonical short name for the absolute position of a node. -/
abbrev position {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : StepField α X) (u : TreeNode α) : X :=
  nodePosition initial step u

@[simp] theorem position_root {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : StepField α X) :
    position initial step [] = initial :=
  nodePosition_root initial step

end Combinatorics.Branching

/-!
# Positions

Canonical import for absolute positions in the Cloud layer.  A position is
an initial value shifted by the total displacement along a path.
-/

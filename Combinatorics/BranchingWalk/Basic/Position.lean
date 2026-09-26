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
  initial + displace step [] u

@[simp] theorem position_root {α X : Type*} [AddCommMonoid X]
    (initial : X) (step : Branching.StepField α X) :
    position initial step [] = initial := by
  simp [position, displace]

namespace RootIndexed

/-- The absolute position of a node in a multi-root walk. -/
def position {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → Branching.StepField α X)
    (r : Root) (u : TreeNode α) : X :=
  initial r + displace (step r) [] u

@[simp] theorem position_root
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → Branching.StepField α X) (r : Root) :
    position initial step r [] = initial r := by
  simp [position, displace]

theorem position_eq_singleRoot
    {Root α X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : Root → Branching.StepField α X)
    (r : Root) (u : TreeNode α) :
    position initial step r u =
      Combinatorics.Branching.position (initial r) (step r) u := by
  rfl

end RootIndexed

end Branching
end Combinatorics

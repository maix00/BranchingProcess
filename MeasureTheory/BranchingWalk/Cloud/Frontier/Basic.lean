import MeasureTheory.BranchingWalk.Cloud.Basic
import Mathlib.Order.Bounds.Basic

/-!
# Deterministic cloud frontiers

`frontier C t` is the set of least positions in the time slice `C.points t`.
It is empty exactly when the slice is empty, and it records all least points
when the order has ties.
-/

namespace MeasureTheory

namespace BranchingWalk

namespace Cloud

variable {Time X : Type*}

/-- The frontier of a cloud at a fixed time: the least points of that time
slice under the given order. -/
def frontier [LE X] (C : Cloud Time X) (t : Time) : Set X :=
  {x | IsLeast {y | y ∈ C.points t} x}

@[simp] theorem mem_frontier_iff [LE X] (C : Cloud Time X) (t : Time)
    (x : X) :
    x ∈ C.frontier t ↔ IsLeast {y | y ∈ C.points t} x :=
  Iff.rfl

theorem frontier_subset_points [LE X] (C : Cloud Time X) (t : Time) :
    C.frontier t ⊆ C.points t := by
  intro x hx
  exact hx.1

end Cloud

end BranchingWalk

end MeasureTheory

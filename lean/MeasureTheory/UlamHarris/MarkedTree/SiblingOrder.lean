import MeasureTheory.UlamHarris.MarkedTree.Basic

/-!
# Sibling order of the marks of a marked tree

A marked tree whose tree enumerates the children of every node from the left
has a distinguished property when the marks are read as the increments that
produced each node: the increment of a later sibling is at least that of an
earlier one. `siblingMonotone` records exactly this condition.

It is the marked-tree side of `BranchingWalk.StandardBranchingWalk`: reading a
marked tree as a step field lists the children of `u` in slot order, and
`parentOrdered` of that step is `siblingMonotone` at `u`
(`BranchingWalk.parentOrdered_stepOfMarkedTree_iff` in
`BranchingWalk/Tree/Correspondence/Basic.lean`).
-/

namespace MeasureTheory

namespace UlamHarris

namespace MarkedTree

variable {α X : Type*} [LT α] [LE X]

/-- The marks of the siblings below a fixed node increase with the slot order:
for `i < j`, whenever both children `u ++ [i]` and `u ++ [j]` are realized, the
mark of the earlier one is at most that of the later one. -/
def siblingMonotone (M : MarkedTree α X) : Prop :=
  ∀ (u : List α) (i j : α)
    (hi : u ++ [i] ∈ M.tree.carrier) (hj : u ++ [j] ∈ M.tree.carrier),
    i < j → M.mark (u ++ [i]) hi ≤ M.mark (u ++ [j]) hj

/-- Sibling monotonicity is a statement about the realized siblings of one
node. -/
theorem siblingMonotone_iff {M : MarkedTree α X} :
    M.siblingMonotone ↔
      ∀ (u : List α) (i j : α)
        (hi : u ++ [i] ∈ M.tree.carrier) (hj : u ++ [j] ∈ M.tree.carrier),
        i < j → M.mark (u ++ [i]) hi ≤ M.mark (u ++ [j]) hj :=
  Iff.rfl

end MarkedTree

end UlamHarris

end MeasureTheory

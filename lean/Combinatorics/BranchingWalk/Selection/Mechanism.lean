import Combinatorics.BranchingWalk.Selection.Contain

/-!
# Selection mechanisms on branching walks

A `SelectionMechanism` is a map `BranchingWalk → BranchingWalk` that always
selects a sub-walk: the image is contained in the source in the `SelectContain`
order, and the image is parent-closed. Containment inherits the mark order
`IsMonotone` automatically, but it does not inherit parent-closure, so the
mechanism declares parent-closure explicitly.

A random selection mechanism is a law on these objects and belongs to the
probability layer. The special mechanisms that bound the number of kept
children by a capacity `N` are the `NSelection`s of `Selection/NSelection/`.
-/

namespace Combinatorics

namespace Branching

namespace Selection

/-- A deterministic selection mechanism: a map on branching walks that keeps a
parent-closed sub-walk of its input, in the `SelectContain` order. -/
structure SelectionMechanism (α X : Type*) [LT α] where
  /-- The selected sub-walk. -/
  select : BranchingWalk α X → BranchingWalk α X
  /-- Selection keeps only particles and children that were already survive. -/
  contained : ∀ β, SelectContain (select β) β
  /-- Selection keeps an initial segment of the children, so the image is
  parent-closed. -/
  parentClosed : ∀ β, IsParentClosed ((select β).step ())

instance (α X : Type*) [LT α] :
    CoeFun (SelectionMechanism α X) (fun _ => BranchingWalk α X → BranchingWalk α X) :=
  ⟨SelectionMechanism.select⟩

namespace SelectionMechanism

variable {α X : Type*} [LT α]

@[ext] theorem ext {M M' : SelectionMechanism α X}
    (h : ∀ β, M.select β = M'.select β) : M = M' := by
  obtain ⟨sel, con, pc⟩ := M
  obtain ⟨sel', con', pc'⟩ := M'
  have hsel : sel = sel' := funext h
  cases hsel
  rw [Subsingleton.elim con con', Subsingleton.elim pc pc']

end SelectionMechanism

end Selection

end Branching

end Combinatorics

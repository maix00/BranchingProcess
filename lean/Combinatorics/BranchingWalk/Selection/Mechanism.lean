import Combinatorics.BranchingWalk.Selection.Contain

/-!
# Selection mechanisms on branching walks

A `SelectionMechanism` is a map `BranchingWalk → BranchingWalk` that always
selects a sub-walk: the image is contained in the source in the `SelectContain`
order, and the image is parent-closed. Containment does not provide an
ordered-step structure after selection; reindexing and ordering are handled
separately. The mechanism therefore declares parent-closure explicitly.

A random selection mechanism is a law on these objects and belongs to the
probability layer. The special mechanisms that bound the number of kept
children by a capacity `N` are the `NSelection`s of `Selection/NSelection/`.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

/-- A deterministic selection mechanism: a map on branching walks that keeps a
parent-closed sub-walk of its input, in the `SelectContain` order. -/
structure RootIndexed.SelectionMechanism
    (Root α Mark Position : Type*) [LT α] where
  /-- The selected sub-walk. -/
  select : RootIndexed.BranchingWalk Root α Mark Position →
    RootIndexed.BranchingWalk Root α Mark Position
  /-- Selection keeps only particles and children that were already survive. -/
  contained : ∀ β, RootIndexed.SelectContain (select β) β
  /-- Selection keeps an initial segment of the children, so the image is
  parent-closed. -/
  parentClosed : ∀ β r, IsParentClosed ((select β).step r)

instance (Root α Mark Position : Type*) [LT α] :
    CoeFun (RootIndexed.SelectionMechanism Root α Mark Position)
      (fun _ => RootIndexed.BranchingWalk Root α Mark Position →
        RootIndexed.BranchingWalk Root α Mark Position) :=
  ⟨RootIndexed.SelectionMechanism.select⟩

namespace RootIndexed.SelectionMechanism

variable {Root α Mark Position : Type*} [LT α]

theorem surviveAlong_parent_of_descendant
    (M : RootIndexed.SelectionMechanism Root α Mark Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u v : TreeNode α)
    (h : surviveAlong ((M β).step r) [] (u ++ v)) :
    surviveAlong ((M β).step r) [] u :=
  M.parentClosed β r u v h

@[ext] theorem ext
    {M M' : RootIndexed.SelectionMechanism Root α Mark Position}
    (h : ∀ β, M.select β = M'.select β) : M = M' := by
  obtain ⟨sel, con, pc⟩ := M
  obtain ⟨sel', con', pc'⟩ := M'
  have hsel : sel = sel' := funext h
  cases hsel
  rw [Subsingleton.elim con con', Subsingleton.elim pc pc']

end RootIndexed.SelectionMechanism

/-- A single-root selection mechanism. -/
abbrev SelectionMechanism (α Mark Position : Type*) [LT α] :=
  RootIndexed.SelectionMechanism PUnit.{1} α Mark Position

/-- The single-root and `PUnit`-root-indexed presentations are identical. -/
def selectionMechanismEquiv (α Mark Position : Type*) [LT α] :
    SelectionMechanism α Mark Position ≃
      RootIndexed.SelectionMechanism PUnit.{1} α Mark Position :=
  Equiv.refl _

end Branching

end Combinatorics

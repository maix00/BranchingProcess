/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.Contain

/-!
# Selection transforms on branching walks

A `WalkTransform` is a map `BranchingWalk → BranchingWalk` that always
selects a sub-walk: the image is contained in the source in the `SelectContain`
order, and the image is parent-closed. Containment does not provide an
ordered-step structure after selection; reindexing and ordering are handled
separately. The mechanism therefore declares parent-closure explicitly.

This whole-walk transform is distinct from the one-generation candidate rule
in `Selection/Basic.lean`. Capacity-bounded transforms are defined alongside
bounded branching walks in `Selection/NSelection/BranchingWalk.lean`.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

/-- A deterministic selection mechanism: a map on branching walks that keeps a
parent-closed sub-walk of its input, in the `SelectContain` order. -/
structure RootIndexed.WalkTransform
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
    CoeFun (RootIndexed.WalkTransform Root α Mark Position)
      (fun _ => RootIndexed.BranchingWalk Root α Mark Position →
        RootIndexed.BranchingWalk Root α Mark Position) :=
  ⟨RootIndexed.WalkTransform.select⟩

namespace RootIndexed.WalkTransform

variable {Root α Mark Position : Type*} [LT α]

theorem surviveAlong_parent_of_descendant
    (M : RootIndexed.WalkTransform Root α Mark Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (u v : TreeNode α)
    (h : surviveAlong ((M β).step r) [] (u ++ v)) :
    surviveAlong ((M β).step r) [] u :=
  M.parentClosed β r u v h

@[ext] theorem ext
    {M M' : RootIndexed.WalkTransform Root α Mark Position}
    (h : ∀ β, M.select β = M'.select β) : M = M' := by
  obtain ⟨sel, con, pc⟩ := M
  obtain ⟨sel', con', pc'⟩ := M'
  have hsel : sel = sel' := funext h
  cases hsel
  rw [Subsingleton.elim con con', Subsingleton.elim pc pc']

end RootIndexed.WalkTransform

/-- A single-root selection mechanism. -/
abbrev WalkTransform (α Mark Position : Type*) [LT α] :=
  RootIndexed.WalkTransform PUnit.{1} α Mark Position

/-- The single-root and `PUnit`-root-indexed presentations are identical. -/
def walkTransformEquiv (α Mark Position : Type*) [LT α] :
    WalkTransform α Mark Position ≃
      RootIndexed.WalkTransform PUnit.{1} α Mark Position :=
  Equiv.refl _

end Branching

end Combinatorics

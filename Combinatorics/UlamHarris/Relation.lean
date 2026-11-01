/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic

/-!
# Relations and parent operation on Ulam--Harris addresses

## Public declarations

* `Combinatorics.UlamHarris.TreeNode.IsChild parent child` means
  `∃ i, child = parent ++ [i]`.
* `Combinatorics.UlamHarris.RootIndexed.parent p` keeps the root of a
  root-indexed address and removes the final child label; roots are fixed.
* `Combinatorics.UlamHarris.RootIndexed.childAddress p i` appends the child
  label `i` to `p` while preserving its root. `parent_childAddress` identifies
  the parent of this address, and `RootIndexed.childAddress_joint_injective` recovers a
  parent and child label uniquely from the resulting address.
* `Combinatorics.UlamHarris.TreeNode.IsChild.length_lt` proves that a child
  address is longer than its parent;
  `Combinatorics.UlamHarris.TreeNode.IsChild.parent_unique` proves uniqueness
  of the parent; and `Combinatorics.UlamHarris.TreeNode.IsChild.irrefl`
  proves that no address is its own child.

This file defines relations on addresses without assuming a realized tree.
`TreeNode.IsChild parent child` means that `child` extends `parent` by exactly
one label. Its direction is parent to child. It is independent of the
survival information in a branching walk.

`RootIndexed.parent` is the structural parent operation on a particle address.
It depends only on the root and address, so it is available before a branching
walk or realized population is introduced.

`RootIndexed.childAddress` is its structural one-step extension. The
parent/child operations are defined for arbitrary address-label types and do
not assume a branching law or a population.

The one-step relation is `\(IsChild(u,v)\iff\exists i,\ v=u++[i]\)`.
For indexed addresses,
`\(parent(r,u++[i])=(r,u)\)` and
`\(childAddress((r,u),i)=(r,u++[i])\)`.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

/-- `child` is a direct child of `parent` in the address tree. -/
def TreeNode.IsChild {α : Type*} (parent child : TreeNode α) : Prop :=
  ∃ i : α, child = parent ++ [i]

namespace RootIndexed

/-- The structural parent of a root-indexed address, obtained by deleting its
last child label while keeping its root. A root is fixed. -/
def parent {Root α : Type*} (p : RootIndexed.TreeNode Root α) :
    RootIndexed.TreeNode Root α :=
  (p.1, p.2.dropLast)

@[simp] theorem fst_parent {Root α : Type*} (p : RootIndexed.TreeNode Root α) :
    (parent p).1 = p.1 := rfl

@[simp] theorem snd_parent {Root α : Type*} (p : RootIndexed.TreeNode Root α) :
    (parent p).2 = p.2.dropLast := rfl

/-- The root address is its own parent. -/
@[simp] theorem parent_root {Root α : Type*} (r : Root) :
    parent (r, ([] : Combinatorics.UlamHarris.TreeNode α)) = (r, []) := by
  simp [parent]

/-- The parent of a child address is the address to which its label was
appended. -/
@[simp] theorem parent_child {Root α : Type*} (r : Root)
    (u : Combinatorics.UlamHarris.TreeNode α) (i : α) :
    parent (r, u ++ [i]) = (r, u) := by
  simp [parent]

/-! Root-preserving child-address operations. -/

/-- Append one child label to a root-indexed address without changing its
root. -/
def childAddress {Root α : Type*}
    (p : RootIndexed.TreeNode Root α) (i : α) :
    RootIndexed.TreeNode Root α :=
  (p.1, p.2 ++ [i])

@[simp] theorem childAddress_fst {Root α : Type*}
    (p : RootIndexed.TreeNode Root α) (i : α) :
    (childAddress p i).1 = p.1 :=
  rfl

@[simp] theorem childAddress_snd {Root α : Type*}
    (p : RootIndexed.TreeNode Root α) (i : α) :
    (childAddress p i).2 = p.2 ++ [i] :=
  rfl

/-- The structural parent of an appended child is its original address. -/
@[simp] theorem parent_childAddress {Root α : Type*}
    (p : RootIndexed.TreeNode Root α) (i : α) :
    parent (childAddress p i) = p := by
  cases p
  simp [childAddress, parent]

/-- A root-indexed child address uniquely determines its parent and final
child label. -/
theorem childAddress_joint_injective {Root α : Type*} :
    Function.Injective (fun pi : RootIndexed.TreeNode Root α × α =>
      childAddress pi.1 pi.2) := by
  rintro ⟨p, i⟩ ⟨q, j⟩ h
  change (p.1, p.2 ++ [i]) = (q.1, q.2 ++ [j]) at h
  obtain ⟨hroot, hlist⟩ := Prod.ext_iff.mp h
  have hparts := List.append_inj' hlist (by simp)
  have hparent : p.2 = q.2 := hparts.1
  have hslot : i = j := by simpa using hparts.2
  cases p
  cases q
  simp_all

end RootIndexed

namespace TreeNode.IsChild

/-- A direct child address is strictly longer than its parent. -/
theorem length_lt {α : Type*} {parent child : TreeNode α}
    (h : IsChild parent child) : parent.length < child.length := by
  rcases h with ⟨i, rfl⟩
  simp [List.length_append]

/-- Every address has at most one parent. -/
theorem parent_unique {α : Type*} {parent₁ parent₂ child : TreeNode α}
    (h₁ : IsChild parent₁ child) (h₂ : IsChild parent₂ child) :
    parent₁ = parent₂ := by
  rcases h₁ with ⟨i, rfl⟩
  rcases h₂ with ⟨j, hj⟩
  have h := congrArg List.dropLast hj
  simpa using h

/-- No address is a direct child of itself. -/
theorem irrefl {α : Type*} (address : TreeNode α) :
    ¬ IsChild address address :=
  fun h => absurd (length_lt h) (Nat.lt_irrefl _)

end TreeNode.IsChild

end UlamHarris

end Combinatorics

end

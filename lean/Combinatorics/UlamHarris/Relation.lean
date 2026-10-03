module

public import Combinatorics.UlamHarris.Basic

/-!
# Relations on Ulam--Harris addresses

This file defines relations on addresses without assuming a realized tree.
`TreeNode.IsChild parent child` means that `child` extends `parent` by exactly
one label. Its direction is parent to child. It is independent of the
survival information in a branching walk.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

/-- `child` is a direct child of `parent` in the address tree. -/
def TreeNode.IsChild {α : Type*} (parent child : TreeNode α) : Prop :=
  ∃ i : α, child = parent ++ [i]

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

namespace Tree

/-- Compatibility name for the former, misleadingly named address relation.
Use `TreeNode.IsChild`, whose name records the parent-to-child direction. -/
@[deprecated TreeNode.IsChild (since := "2026-10-03")]
def siblingRel {α : Type*} (a b : TreeNode α) : Prop :=
  TreeNode.IsChild a b

@[simp, deprecated TreeNode.IsChild +typeChanged (since := "2026-10-03")]
theorem siblingRel_def {α : Type*} {a b : TreeNode α} :
    siblingRel a b ↔ ∃ i : α, b = a ++ [i] :=
  Iff.rfl

/-- Compatibility theorem for `TreeNode.IsChild.length_lt`. -/
@[deprecated TreeNode.IsChild.length_lt +typeChanged (since := "2026-10-03")]
theorem siblingRel_length_lt {α : Type*} {a b : TreeNode α}
    (h : siblingRel a b) : a.length < b.length :=
  TreeNode.IsChild.length_lt h

/-- Compatibility theorem for `TreeNode.IsChild.parent_unique`. -/
@[deprecated TreeNode.IsChild.parent_unique +typeChanged (since := "2026-10-03")]
theorem siblingRel_left_unique {α : Type*} {a b c : TreeNode α}
    (hab : siblingRel a c) (hbc : siblingRel b c) : a = b :=
  TreeNode.IsChild.parent_unique hab hbc

/-- Compatibility theorem for `TreeNode.IsChild.irrefl`. -/
@[deprecated TreeNode.IsChild.irrefl +typeChanged (since := "2026-10-03")]
theorem siblingRel_irrefl {α : Type*} (a : TreeNode α) : ¬ siblingRel a a :=
  TreeNode.IsChild.irrefl a

end Tree

end UlamHarris

end Combinatorics

end

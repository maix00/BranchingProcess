import Combinatorics.UlamHarris.Tree.Basic

/-!
# The generation of an address, and the generations between two addresses

`generation u` is the length of the address `u`, that is the number of edges from the root, the
level at which the node sits. `generationAfter u v` is the number of generations from `u` down to
`v`: the length of the segment of `v` below `u`, so `0` when `v` is `u` itself, `1` on a child, and
the length of the surviving segment on a descendant. Both notions use addresses only, so they live
with the tree rather than with any walk.

The levels of `generation` are what `Tree/Truncation.lean` cuts at and what `Tree/Height.lean`
compares; `generationAfter` is the tree distance in the ancestor-descendant case, an ordinary
natural number rather than the `ℕ∞`-valued height used there, because a node is finitely far below
its own ancestor.
-/

open Combinatorics.UlamHarris

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*}

/-- The generation of an address: its length, the number of edges from the root. -/
def generation (u : TreeNode α) : ℕ :=
  u.length

@[simp] theorem generation_def (u : TreeNode α) : generation u = u.length := rfl

/-- The root is at generation zero. -/
@[simp] theorem generation_nil : generation ([] : TreeNode α) = 0 := rfl

/-- Generations add along an extension of an address. -/
theorem generation_append (u p : TreeNode α) :
    generation (u ++ p) = generation u + generation p := by
  simp [generation]

/-- The number of generations from `u` down to `v`: the length of the segment of `v` below `u`. -/
def generationAfter (u v : TreeNode α) : ℕ :=
  (v.drop (generation u)).length

/-- On a descendant, the number of generations below an ancestor is the length of the segment
below it. -/
theorem generationAfter_eq_length {u v p : TreeNode α} (hp : v = u ++ p) :
    generationAfter u v = p.length := by
  rw [generationAfter, generation, hp, List.drop_left]

/-- A node is zero generations below itself. -/
@[simp] theorem generationAfter_self (u : TreeNode α) : generationAfter u u = 0 := by
  simp [generationAfter, generation]

/-- A child is one generation below its parent. -/
@[simp] theorem generationAfter_append_singleton (u : TreeNode α) (i : α) :
    generationAfter u (u ++ [i]) = 1 := by
  rw [generationAfter_eq_length rfl]
  rfl

/-- Generation distances add: the generations below `u` to a descendant of `u ++ p` are those
below `u` to `u ++ p` plus those below `u ++ p` to the descendant. -/
theorem generationAfter_append_append (u p q : TreeNode α) :
    generationAfter u (u ++ (p ++ q)) =
      generationAfter u (u ++ p) + generationAfter (u ++ p) (u ++ (p ++ q)) := by
  rw [generationAfter_eq_length (u := u) (v := u ++ (p ++ q)) (p := p ++ q) rfl,
    generationAfter_eq_length (u := u) (v := u ++ p) (p := p) rfl,
    generationAfter_eq_length (u := u ++ p) (v := u ++ (p ++ q)) (p := q)
      (List.append_assoc u p q).symm]
  simp

end Tree

end UlamHarris

end Combinatorics

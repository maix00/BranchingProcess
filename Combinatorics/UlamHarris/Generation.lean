module

public import Combinatorics.UlamHarris.Basic
public import Combinatorics.UlamHarris.Tree.Basic

/-!
# The generation of a particle, and the generations between two particles

`RootIndexed.generation p` is the length of the address of the particle `p`, the level it sits at:
the notion only looks at a `TreeNode`, so it is indexed by whatever the address is paired with, and
that pairing is what makes the `Root × TreeNode` case of the cloud available. `RootIndexed.generationAfter p q`
is the number of generations from `p` down to `q`, the length of the segment of `q`'s address below
`p`'s.

The plain forms `generation u` and `generationAfter u v` on addresses alone are the same notions read
without a root, defined from the indexed ones at the one-point root.

The levels of `generation` are what `Tree/Truncation.lean` cuts at and what `Tree/Height.lean`
compares; `generationAfter` is the tree distance in the ancestor-descendant case, an ordinary natural
number rather than the `ℕ∞`-valued height used there, because a node is finitely far below its own
ancestor.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed

/-- The generation of a particle: the length of its address, the number of edges from the root. -/
def generation {Root α : Type*} (p : RootIndexed.TreeNode Root α) : ℕ :=
  p.2.length

@[simp] theorem generation_def {Root α : Type*} (p : RootIndexed.TreeNode Root α) :
    generation p = p.2.length := rfl

@[simp] theorem generation_mk {Root α : Type*} (r : Root) (u : UlamHarris.TreeNode α) :
    generation (r, u) = u.length := rfl

/-- Generations add along an extension of the address of a particle. -/
theorem generation_append {Root α : Type*} (p : RootIndexed.TreeNode Root α) (t : UlamHarris.TreeNode α) :
    generation (p.1, p.2 ++ t) = generation p + t.length := by
  simp [generation, List.length_append]

/-- The number of generations from `p` down to `q`: the length of the segment of `q`'s address
below the address of `p`. -/
def generationAfter {Root α : Type*} (p q : RootIndexed.TreeNode Root α) : ℕ :=
  (q.2.drop (generation p)).length

/-- On a descendant, the number of generations below an ancestor is the length of the segment below
it. -/
theorem generationAfter_eq_length {Root α : Type*} {p q : RootIndexed.TreeNode Root α} {t : UlamHarris.TreeNode α}
    (hq : q.2 = p.2 ++ t) : generationAfter p q = t.length := by
  rw [generationAfter, generation, hq, List.drop_left]

/-- A particle is zero generations below itself. -/
@[simp] theorem generationAfter_self {Root α : Type*} (p : RootIndexed.TreeNode Root α) :
    generationAfter p p = 0 := by
  simp [generationAfter, generation]

/-- A child is one generation below its parent. -/
@[simp] theorem generationAfter_append_singleton {Root α : Type*} (p : RootIndexed.TreeNode Root α) (i : α) :
    generationAfter p (p.1, p.2 ++ [i]) = 1 := by
  rw [generationAfter_eq_length rfl]
  rfl

/-- Generation distances add: the generations below `p` to a descendant of `p.1, p.2 ++ s` are those
below `p` to `p.1, p.2 ++ s` plus those below it to the descendant. -/
theorem generationAfter_append_append {Root α : Type*} (p : RootIndexed.TreeNode Root α) (s t : UlamHarris.TreeNode α) :
    generationAfter p (p.1, p.2 ++ (s ++ t)) =
      generationAfter p (p.1, p.2 ++ s) +
        generationAfter (p.1, p.2 ++ s) (p.1, p.2 ++ (s ++ t)) := by
  rw [generationAfter_eq_length (p := p) (q := (p.1, p.2 ++ (s ++ t))) (t := s ++ t) rfl,
    generationAfter_eq_length (p := p) (q := (p.1, p.2 ++ s)) (t := s) rfl,
    generationAfter_eq_length (p := (p.1, p.2 ++ s)) (q := (p.1, p.2 ++ (s ++ t))) (t := t)
      (by simp [List.append_assoc])]
  simp

end RootIndexed

/-- The generation of an address: the length of the address, the number of edges from the root. The
indexed form at the one-point root. -/
def generation {α : Type*} (u : TreeNode α) : ℕ :=
  u.length

/-- The plain generation is the indexed one at the one-point root, which is how the indexed form
covers addresses read without a root. -/
theorem generation_eq_rootIndexed {Root α : Type*} (r : Root) (u : TreeNode α) :
    generation u = RootIndexed.generation (r, u) := rfl

@[simp] theorem generation_def {α : Type*} (u : TreeNode α) : generation u = u.length := rfl

/-- The root is at generation zero. -/
@[simp] theorem generation_nil : generation ([] : TreeNode α) = 0 := rfl

/-- Generations add along an extension of an address. -/
theorem generation_append {α : Type*} (u p : TreeNode α) :
    generation (u ++ p) = generation u + generation p := by
  simp [generation, List.length_append]

/-- The number of generations from `u` down to `v`: the length of the segment of `v` below `u`. -/
def generationAfter {α : Type*} (u v : TreeNode α) : ℕ :=
  (v.drop (generation u)).length

/-- The plain generation distance is the indexed one at the one-point root. -/
theorem generationAfter_eq_rootIndexed {Root α : Type*} (r : Root) (u v : TreeNode α) :
    generationAfter u v = RootIndexed.generationAfter (r, u) (r, v) := rfl

/-- On a descendant, the number of generations below an ancestor is the length of the segment below
it. -/
theorem generationAfter_eq_length {α : Type*} {u v p : TreeNode α} (hp : v = u ++ p) :
    generationAfter u v = p.length := by
  rw [generationAfter, generation, hp, List.drop_left]

/-- A node is zero generations below itself. -/
@[simp] theorem generationAfter_self {α : Type*} (u : TreeNode α) : generationAfter u u = 0 := by
  simp [generationAfter, generation]

/-- A child is one generation below its parent. -/
@[simp] theorem generationAfter_append_singleton {α : Type*} (u : TreeNode α) (i : α) :
    generationAfter u (u ++ [i]) = 1 := by
  rw [generationAfter_eq_length rfl]
  rfl

/-- Generation distances add. -/
theorem generationAfter_append_append {α : Type*} (u p q : TreeNode α) :
    generationAfter u (u ++ (p ++ q)) =
      generationAfter u (u ++ p) + generationAfter (u ++ p) (u ++ (p ++ q)) := by
  rw [generationAfter_eq_length (u := u) (v := u ++ (p ++ q)) (p := p ++ q) rfl,
    generationAfter_eq_length (u := u) (v := u ++ p) (p := p) rfl,
    generationAfter_eq_length (u := u ++ p) (v := u ++ (p ++ q)) (p := q)
      (List.append_assoc u p q).symm]
  simp

end UlamHarris

end Combinatorics

end

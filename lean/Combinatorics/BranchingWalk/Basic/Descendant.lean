import Combinatorics.BranchingWalk.Basic.Definitions

/-!
# Descendants of a node in a branching walk

A node `v` is a descendant of a node `u` for a root `r` when the part of `v` below `u` is a path
that survives from `u` along the root's step field. The notion is built on `surviveAlong`, so the
tree of a walk is described by the same recursion as the steps themselves, and it is the
predicate that the rank restricted to descendants counts.

The particles of the cloud `Cloud.ofBranchingWalk β time` are exactly the root-address pairs whose
address is a descendant of the empty address at a matching time; that link lives with the cloud,
since this folder does not know about time.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α X : Type*}

/-- `v` is a descendant of `u` in the tree realized by the root `r`: the part of `v` below `u`,
if any, is a path that survives from `u`. -/
def RootIndexed.BranchingWalk.IsDescendant (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u v : TreeNode α) : Prop :=
  ∃ p, v = u ++ p ∧ surviveAlong (β.step r) u p

/-- Every node is a descendant of itself. -/
theorem RootIndexed.BranchingWalk.isDescendant_refl (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) : β.IsDescendant r u u :=
  ⟨[], (List.append_nil u).symm, trivial⟩

/-- The descendants of a node at one step are the children whose slot survives. -/
theorem RootIndexed.BranchingWalk.isDescendant_append_singleton_iff
    (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α) (i : α) :
    β.IsDescendant r u (u ++ [i]) ↔ survive (β.step r u) i := by
  constructor
  · rintro ⟨p, hp, hs⟩
    have hpi : p = [i] := List.append_cancel_left hp.symm
    subst hpi
    simpa [surviveAlong] using hs
  · intro hi
    exact ⟨[i], rfl, by simpa [surviveAlong] using hi⟩

/-- Descendants compose: a descendant of a descendant is a descendant. -/
theorem RootIndexed.BranchingWalk.isDescendant_trans (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    {u v w : TreeNode α} (huv : β.IsDescendant r u v) (hvw : β.IsDescendant r v w) :
    β.IsDescendant r u w := by
  obtain ⟨p, hp, hs⟩ := huv
  obtain ⟨q, hq, hs'⟩ := hvw
  refine ⟨p ++ q, by rw [hq, hp, List.append_assoc], ?_⟩
  rw [surviveAlong_append]
  exact ⟨hs, hp ▸ hs'⟩

/-- A node is a descendant of `u` exactly when it is realized at a time at least that of `u`...
The empty address is below everything: the descendants of the empty address are the realized
addresses of the root. -/
theorem RootIndexed.BranchingWalk.isDescendant_nil_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) : β.IsDescendant r [] u ↔ surviveAlong (β.step r) [] u := by
  refine ⟨fun h => ?_, fun h => ⟨u, (List.nil_append u).symm, h⟩⟩
  obtain ⟨p, hp, hs⟩ := h
  rwa [show p = u from by simpa using hp.symm] at hs

/-- The number of generations from `u` down to `v`: the length of the segment of `v` below `u`.
It depends on the addresses only, not on the walk, and it is zero exactly when `v` is a prefix of
`u`... in particular when `v = u`. Together with `RootIndexed.BranchingWalk.IsDescendant` it says
how far below an ancestor a node stands, which is what the generation of a particle measures
absolutely as the length of its address. -/
def generationsBelow {α : Type*} (u v : TreeNode α) : ℕ :=
  (v.drop u.length).length

/-- A node stands zero generations below itself. -/
@[simp] theorem generationsBelow_self {α : Type*} (u : TreeNode α) :
    generationsBelow u u = 0 := by
  simp [generationsBelow]

/-- The number of generations below an ancestor is the length of the segment below it. -/
theorem generationsBelow_eq_length {α : Type*} {u v p : TreeNode α} (hp : v = u ++ p) :
    generationsBelow u v = p.length := by
  rw [generationsBelow, hp, List.drop_left]

/-- A child stands one generation below its parent. -/
@[simp] theorem generationsBelow_append_singleton {α : Type*} (u : TreeNode α) (i : α) :
    generationsBelow u (u ++ [i]) = 1 := by
  rw [generationsBelow_eq_length rfl]
  rfl

/-- Generation distances add: the generations below `u` to a descendant of `u ++ p` are those
below `u` to `u ++ p` plus those below `u ++ p` to the descendant. -/
theorem generationsBelow_append_append {α : Type*} (u p q : TreeNode α) :
    generationsBelow u (u ++ (p ++ q)) =
      generationsBelow u (u ++ p) + generationsBelow (u ++ p) (u ++ (p ++ q)) := by
  rw [generationsBelow_eq_length (u := u) (v := u ++ (p ++ q)) (p := p ++ q) rfl,
    generationsBelow_eq_length (u := u) (v := u ++ p) (p := p) rfl,
    generationsBelow_eq_length (u := u ++ p) (v := u ++ (p ++ q)) (p := q)
      (List.append_assoc u p q).symm]
  simp

/-- A strict descendant stands at least one generation below its ancestor. -/
theorem generationsBelow_pos_of_isDescendant {Root α X : Type*}
    (β : RootIndexed.BranchingWalk Root α X) (r : Root) {u v : TreeNode α}
    (h : β.IsDescendant r u v) (hne : v ≠ u) : 0 < generationsBelow u v := by
  obtain ⟨p, hp, -⟩ := h
  have hpne : p ≠ [] := fun hnil => hne (by rw [hp, hnil, List.append_nil])
  rw [generationsBelow_eq_length hp]
  exact List.length_pos_iff.mpr hpne

end Combinatorics.Branching

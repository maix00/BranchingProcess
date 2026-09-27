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

end Combinatorics.Branching

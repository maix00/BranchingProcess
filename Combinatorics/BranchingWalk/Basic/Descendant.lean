import Combinatorics.BranchingWalk.Basic.Definitions
import Combinatorics.UlamHarris.Tree.Generation

/-!
# Descendants of a node in a branching walk

A node `v` is a descendant of a node `u` for a root `r` when the part of `v` below `u` is a path
that survives from `u` along the root's step field. The notion is built on `surviveAlong`, so the
tree of a walk is described by the same recursion as the steps themselves.

On top of it sit the descendant set of a node and, for every number of generations below it, the
slice of the descendants that are exactly that far below. The generations themselves are
`Tree.generation` (the length of an address) and `Tree.generationAfter` (the generations between a
node and a descendant), which belong to the tree and live in `UlamHarris/Tree/Generation.lean`.

The particles of the cloud `Cloud.ofBranchingWalk β time` are exactly the root-address pairs whose
address is a descendant of the empty address at a matching time; that link lives with the cloud,
since this folder does not know about time.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

variable {Root α X : Type*}

/-- `v` is a descendant of `u` in the tree realized by the root `r`: the part of `v` below `u`,
if any, is a path that survives from `u`. -/
def IsDescendant (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u v : TreeNode α) : Prop :=
  ∃ p, v = u ++ p ∧ surviveAlong (β.step r) u p

/-- Every node is a descendant of itself. -/
theorem isDescendant_refl (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) : IsDescendant β r u u :=
  ⟨[], (List.append_nil u).symm, trivial⟩

/-- The descendants of a node at one step are the children whose slot survives. -/
theorem isDescendant_append_singleton_iff
    (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α) (i : α) :
    IsDescendant β r u (u ++ [i]) ↔ survive (β.step r u) i := by
  constructor
  · rintro ⟨p, hp, hs⟩
    have hpi : p = [i] := List.append_cancel_left hp.symm
    subst hpi
    simpa [surviveAlong] using hs
  · intro hi
    exact ⟨[i], rfl, by simpa [surviveAlong] using hi⟩

/-- Descendants compose: a descendant of a descendant is a descendant. -/
theorem isDescendant_trans (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    {u v w : TreeNode α} (huv : IsDescendant β r u v) (hvw : IsDescendant β r v w) :
    IsDescendant β r u w := by
  obtain ⟨p, hp, hs⟩ := huv
  obtain ⟨q, hq, hs'⟩ := hvw
  refine ⟨p ++ q, by rw [hq, hp, List.append_assoc], ?_⟩
  rw [surviveAlong_append]
  exact ⟨hs, hp ▸ hs'⟩

/-- The descendants of the empty address are the realized addresses of the root. -/
theorem isDescendant_nil_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) : IsDescendant β r [] u ↔ surviveAlong (β.step r) [] u := by
  refine ⟨fun h => ?_, fun h => ⟨u, (List.nil_append u).symm, h⟩⟩
  obtain ⟨p, hp, hs⟩ := h
  rwa [show p = u from by simpa using hp.symm] at hs

/-- A descendant's own generation is the generation of its ancestor plus the generations
between them. -/
theorem generation_eq_generation_add_of_isDescendant (β : RootIndexed.BranchingWalk Root α X)
    (r : Root) {u v : TreeNode α} (hv : IsDescendant β r u v) :
    Tree.generation v = Tree.generation u + Tree.generationAfter u v := by
  obtain ⟨p, hp, -⟩ := hv
  rw [hp, Tree.generation_append, Tree.generationAfter_eq_length (u := u) (v := u ++ p) (p := p) rfl]
  simp [Tree.generation]

/-- The descendants of a node, as a set of addresses. -/
def descendants (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α) :
    Set (TreeNode α) :=
  {v | IsDescendant β r u v}

@[simp] theorem mem_descendants_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u v : TreeNode α) : v ∈ descendants β r u ↔ IsDescendant β r u v := Iff.rfl

/-- The descendants of a node exactly `k` generations below it. -/
def descendantsAt (β : RootIndexed.BranchingWalk Root α X) (r : Root) (u : TreeNode α)
    (k : ℕ) : Set (TreeNode α) :=
  {v | IsDescendant β r u v ∧ Tree.generationAfter u v = k}

@[simp] theorem mem_descendantsAt_iff (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) (k : ℕ) (v : TreeNode α) :
    v ∈ descendantsAt β r u k ↔ IsDescendant β r u v ∧ Tree.generationAfter u v = k := Iff.rfl

/-- A generation slice consists of descendants. -/
theorem mem_descendants_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    {u v : TreeNode α} {k : ℕ} (hv : v ∈ descendantsAt β r u k) : v ∈ descendants β r u :=
  hv.1

/-- The number of generations below an ancestor on the generation slice is the one cutting it. -/
theorem generationAfter_of_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    {u v : TreeNode α} {k : ℕ} (hv : v ∈ descendantsAt β r u k) :
    Tree.generationAfter u v = k :=
  hv.2

/-- Different generations below a node are disjoint. -/
theorem disjoint_descendantsAt (β : RootIndexed.BranchingWalk Root α X) (r : Root)
    (u : TreeNode α) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (descendantsAt β r u k) (descendantsAt β r u l) := by
  rw [Set.disjoint_left]
  intro v hv hw
  exact hkl (by rw [← hv.2, hw.2])

/-- A node is a descendant exactly when it lies in one of the generation slices, which is what
makes those slices a partition of the descendants. -/
theorem mem_descendants_iff_exists_mem_descendantsAt (β : RootIndexed.BranchingWalk Root α X)
    (r : Root) (u v : TreeNode α) :
    v ∈ descendants β r u ↔ ∃ k : ℕ, v ∈ descendantsAt β r u k :=
  ⟨fun hv => ⟨Tree.generationAfter u v, hv, rfl⟩, fun ⟨_, hk⟩ => hk.1⟩

end Combinatorics.Branching

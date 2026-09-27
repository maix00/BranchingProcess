import Combinatorics.BranchingWalk.Tree.Correspondence.Basic
import Combinatorics.UlamHarris.MarkedTree.RootIndexed.Basic

/-!
# The marked tree of a branching walk

`RootIndexed.BranchingWalk.markedTree β` is the marked tree of the walk itself, one tree for each
initial ancestor: the realized addresses of the root `r` are the ones whose root path survives in
`β.step r`, and each of them carries its displacement from `r`. The construction reads the walk and
nothing else, so the object it produces is `UlamHarris.RootIndexed.MarkedTree Root α X`, the
root-indexed marked object, and not a single-root one.

The single-root reading is a bridge: for a walk with one initial ancestor the tree at that ancestor is
the marked tree of the corresponding step field (`markedTree_apply`), which is where the per-root
computations of `Tree/Correspondence/Basic.lean` are reused. Sibling closure of every step is assumed,
since a tree is sibling closed and a walk does not carry that condition.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Root α X : Type*}

section AddCommGroup

variable [LT α] [AddCommGroup X]

/-- The marked tree of a branching walk, one tree for each initial ancestor: the realized addresses of
the root `r` carry their displacement `displace (β.step r) [] u`. The tree is sibling closed exactly
because each step is, and parent closed because a prefix of a realized path is realized. -/
noncomputable def RootIndexed.BranchingWalk.markedTree (β : RootIndexed.BranchingWalk Root α X)
    (hsib : ∀ r, ∀ u, Step.IsSiblingClosed (β.step r u)) :
    UlamHarris.RootIndexed.MarkedTree Root α X :=
  fun r =>
    { tree :=
        { carrier := {u | surviveAlong (β.step r) [] u}
          root_mem := surviveAlong_nil (β.step r) []
          parent_closed := by
            intro u v h
            exact surviveAlong_prefix (β.step r) u v h
          sibling_closed := by
            intro u i j hmem hij
            have hmem' : surviveAlong (β.step r) [] (u ++ [j]) := hmem
            change surviveAlong (β.step r) [] (u ++ [i])
            rw [surviveAlong_root_append_singleton_iff] at hmem'
            rw [surviveAlong_root_append_singleton_iff]
            exact ⟨hmem'.1, (survive_iff_ne_none _ _).2 fun hnone =>
              ((survive_iff_ne_none _ _).1 hmem'.2) ((hsib r u) i j hij hnone)⟩ }
      mark := fun u _ => displace (β.step r) [] u }

/-- The realized addresses of the marked tree of a walk are the surviving addresses of that root. -/
@[simp] theorem RootIndexed.BranchingWalk.mem_markedTree_carrier
    (β : RootIndexed.BranchingWalk Root α X)
    (hsib : ∀ r, ∀ u, Step.IsSiblingClosed (β.step r u)) (r : Root) (u : TreeNode α) :
    u ∈ (β.markedTree hsib r).tree.carrier ↔ surviveAlong (β.step r) [] u :=
  Iff.rfl

/-- The mark of a realized address of the marked tree of a walk is its displacement from the root. -/
@[simp] theorem RootIndexed.BranchingWalk.markedTree_mark (β : RootIndexed.BranchingWalk Root α X)
    (hsib : ∀ r, ∀ u, Step.IsSiblingClosed (β.step r u)) (r : Root) (u : TreeNode α)
    (h : u ∈ (β.markedTree hsib r).tree.carrier) :
    (β.markedTree hsib r).mark u h = displace (β.step r) [] u := rfl

/-- The bridge to the single-root reading: for a walk with one initial ancestor, the marked tree of the
walk at that ancestor is the marked tree of its step field, which is where the per-root computations
of `Tree/Correspondence/Basic.lean` are reused. -/
theorem RootIndexed.BranchingWalk.markedTree_apply (β : RootIndexed.BranchingWalk PUnit α X)
    (hsib : ∀ u, Step.IsSiblingClosed (β.step PUnit.unit u)) :
    β.markedTree (fun _ => hsib) PUnit.unit = markedTreeOfStep (β.step PUnit.unit) hsib :=
  rfl

end AddCommGroup

end Branching

end Combinatorics

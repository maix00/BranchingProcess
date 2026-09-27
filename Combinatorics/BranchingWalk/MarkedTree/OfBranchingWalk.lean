import Combinatorics.BranchingWalk.MarkedTree.Equivalence
import Combinatorics.BranchingWalk.Basic.Orderable
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
computations of `MarkedTree/Equivalence.lean` are reused. Sibling closure of every step is assumed,
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
    (hsib : ∀ r, IsSiblingClosed (β.step r)) :
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
    (hsib : ∀ r, IsSiblingClosed (β.step r)) (r : Root) (u : TreeNode α) :
    u ∈ (β.markedTree hsib r).tree.carrier ↔ surviveAlong (β.step r) [] u :=
  Iff.rfl

/-- The mark of a realized address of the marked tree of a walk is its displacement from the root. -/
@[simp] theorem RootIndexed.BranchingWalk.markedTree_mark (β : RootIndexed.BranchingWalk Root α X)
    (hsib : ∀ r, IsSiblingClosed (β.step r)) (r : Root) (u : TreeNode α)
    (h : u ∈ (β.markedTree hsib r).tree.carrier) :
    (β.markedTree hsib r).mark u h = displace (β.step r) [] u := rfl

/-- The bridge to the single-root reading: for a walk with one initial ancestor, the marked tree of the
walk at that ancestor is the marked tree of its step field, which is where the per-root computations
of `MarkedTree/Equivalence.lean` are reused. -/
theorem RootIndexed.BranchingWalk.markedTree_apply (β : RootIndexed.BranchingWalk PUnit α X)
    (hsib : IsSiblingClosed (β.step PUnit.unit)) :
    β.markedTree (fun _ => hsib) PUnit.unit = markedTreeOfStep (β.step PUnit.unit) hsib :=
  rfl

/-- The marked tree of a sibling closable walk, one tree for each initial ancestor: the step field of
every root is read along the relabelings its closability supplies. -/
noncomputable def RootIndexed.BranchingWalk.markedTreeOfClosable
    (β : RootIndexed.BranchingWalk Root α X)
    (h : RootIndexed.BranchingWalk.IsSiblingClosable β) :
    UlamHarris.RootIndexed.MarkedTree Root α X :=
  fun r => (β.step r).markedTreeOfClosable (h.pointwise r)

/-- On a sibling closable slot type the marked tree of a walk is had with nothing handed in. -/
noncomputable def RootIndexed.BranchingWalk.markedTreeOfClosable'
    [Combinatorics.Branching.IsSiblingClosable α] (β : RootIndexed.BranchingWalk Root α X) :
    UlamHarris.RootIndexed.MarkedTree Root α X :=
  β.markedTreeOfClosable inferInstance

/-- The marked tree of an orderable step field: read the field along the relabelling its orderability
supplies. The relabelled steps are sibling closed, which is what the tree needs, so the children of every
node sit on an initial segment with increasing marks. -/
noncomputable def StepField.markedTreeOfOrderable [LinearOrder X] (β : StepField ℕ X)
    (h : β.IsOrderable) :
    MarkedTree ℕ X :=
  markedTreeOfStep (fun u => (β u).order (h.pointwise u))
    fun u => ((β u).order_isOrdered (h.pointwise u)).1

/-- On a finitely supported step field the ordered marked tree is had with nothing handed in: the field is
orderable by instance search. -/
noncomputable def StepField.markedTreeOfOrderable' [LinearOrder X] (β : StepField ℕ X)
    [h : StepField.IsFinitelySupported β] : MarkedTree ℕ X :=
  β.markedTreeOfOrderable inferInstance

/-- The marked tree of an orderable walk, one tree for each initial ancestor. -/
noncomputable def RootIndexed.BranchingWalk.markedTreeOfOrderable [LinearOrder X]
    (β : RootIndexed.BranchingWalk Root ℕ X) (h : β.IsOrderable) :
    UlamHarris.RootIndexed.MarkedTree Root ℕ X :=
  fun r => (β.step r).markedTreeOfOrderable (h.pointwise r)

/-- On a finitely supported walk the ordered marked tree is had with nothing handed in. -/
noncomputable def RootIndexed.BranchingWalk.markedTreeOfOrderable' [LinearOrder X]
    (β : RootIndexed.BranchingWalk Root ℕ X) [h : RootIndexed.BranchingWalk.IsFinitelySupported β] :
    UlamHarris.RootIndexed.MarkedTree Root ℕ X :=
  β.markedTreeOfOrderable inferInstance

end AddCommGroup

end Branching

end Combinatorics

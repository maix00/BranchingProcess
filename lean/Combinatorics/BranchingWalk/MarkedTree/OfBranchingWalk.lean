module

public import Combinatorics.BranchingWalk.MarkedTree.Equivalence
public import Combinatorics.BranchingWalk.Basic.Orderable
public import Combinatorics.BranchingWalk.Basic.DisplacementMap
public import Combinatorics.UlamHarris.MarkedTree.Basic

@[expose] public section

/-!
# The marked tree of a branching walk

`RootIndexed.BranchingWalk.markedTreeWith` builds the realized genealogical tree
and accepts an arbitrary dependent node-marking function.  In particular, the
mark type is independent of both the edge-mark type and the position type.
`positionedMarkedTree` is the specialization whose node marks are accumulated
positions obtained through a displacement map.

The single-root reading is a bridge: for a walk with one initial ancestor the tree at that ancestor is
the marked tree of the corresponding step field (`markedTree_apply`), which is where the per-root
computations of `MarkedTree/Equivalence.lean` are reused. Sibling closure of every step is assumed,
since a tree is sibling closed and a walk does not carry that condition.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Root α Mark Position M : Type*}

section General

variable [LT α]

/-- Put arbitrary node metadata on the realized genealogical trees of a walk.
The metadata may depend on the proof that the node is realized. -/
noncomputable def RootIndexed.BranchingWalk.markedTreeWith
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (hsib : ∀ r, IsSiblingClosed (β.step r))
    (nodeMark : ∀ r u, surviveAlong (β.step r) [] u → M) :
    UlamHarris.RootIndexed.MarkedTree Root α M :=
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
      mark := fun u h => nodeMark r u h }

/-- Mark realized nodes by their accumulated displacement in an independent
position space. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTree
    [AddCommMonoid Position]
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) (hsib : ∀ r, IsSiblingClosed (β.step r)) :
    UlamHarris.RootIndexed.MarkedTree Root α Position :=
  β.markedTreeWith hsib (fun r u _ => displaceWith d (β.step r) [] u)

/-- The realized addresses of the marked tree of a walk are the surviving addresses of that root. -/
@[simp] theorem RootIndexed.BranchingWalk.mem_markedTree_carrier
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (hsib : ∀ r, IsSiblingClosed (β.step r))
    (nodeMark : ∀ r u, surviveAlong (β.step r) [] u → M)
    (r : Root) (u : TreeNode α) :
    u ∈ (β.markedTreeWith hsib nodeMark r).tree.carrier ↔ surviveAlong (β.step r) [] u :=
  Iff.rfl

@[simp] theorem RootIndexed.BranchingWalk.markedTreeWith_mark
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (hsib : ∀ r, IsSiblingClosed (β.step r))
    (nodeMark : ∀ r u, surviveAlong (β.step r) [] u → M)
    (r : Root) (u : TreeNode α)
    (h : u ∈ (β.markedTreeWith hsib nodeMark r).tree.carrier) :
    (β.markedTreeWith hsib nodeMark r).mark u h = nodeMark r u h := rfl

/-- The mark of a realized address of the marked tree of a walk is its displacement from the root. -/
@[simp] theorem RootIndexed.BranchingWalk.positionedMarkedTree_mark
    [AddCommMonoid Position]
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) (hsib : ∀ r, IsSiblingClosed (β.step r))
    (r : Root) (u : TreeNode α)
    (h : u ∈ (β.positionedMarkedTree d hsib r).tree.carrier) :
    (β.positionedMarkedTree d hsib r).mark u h =
      displaceWith d (β.step r) [] u := rfl

section AddCommGroup

variable [AddCommGroup Position]

/-- The bridge to the single-root reading: for a walk with one initial ancestor, the marked tree of the
walk at that ancestor is the marked tree of its step field, which is where the per-root computations
of `MarkedTree/Equivalence.lean` are reused. -/
theorem RootIndexed.BranchingWalk.positionedMarkedTree_apply
    (β : RootIndexed.BranchingWalk PUnit α Position Position)
    (hsib : IsSiblingClosed (β.step PUnit.unit)) :
    β.positionedMarkedTree id (fun _ => hsib) PUnit.unit =
      markedTreeOfStep (β.step PUnit.unit) hsib := by
  have htree : (β.positionedMarkedTree id (fun _ => hsib) PUnit.unit).tree =
      (markedTreeOfStep (β.step PUnit.unit) hsib).tree := rfl
  refine MarkedTree.ext htree ?_
  intro u hu
  simp [RootIndexed.BranchingWalk.positionedMarkedTree,
    RootIndexed.BranchingWalk.markedTreeWith, markedTreeOfStep]

/-- The marked tree of a sibling closable walk, one tree for each initial ancestor: the step field of
every root is read along the relabelings its closability supplies. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTreeOfClosable
    {Mark : Type*} (β : RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position)
    (h : RootIndexed.BranchingWalk.IsSiblingClosable β) :
    UlamHarris.RootIndexed.MarkedTree Root α Position :=
  fun r => (β.step r).positionedMarkedTreeOfClosable d (h.pointwise r)

/-- On a sibling closable slot type the marked tree of a walk is had with nothing handed in. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTreeOfClosable'
    {Mark : Type*}
    [Combinatorics.Branching.IsSiblingClosable α]
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (d : Mark → Position) :
    UlamHarris.RootIndexed.MarkedTree Root α Position :=
  β.positionedMarkedTreeOfClosable d inferInstance

/-- The marked tree of an orderable step field: read the field along the relabelling its orderability
supplies. The relabelled steps are sibling closed, which is what the tree needs, so the children of every
node sit on an initial segment with increasing marks. -/
noncomputable def StepField.markedTreeOfOrderable [LinearOrder Position]
    (β : StepField ℕ Position)
    (h : β.IsOrderable) :
    MarkedTree ℕ Position :=
  markedTreeOfStep (fun u => (β u).order (h.pointwise u))
    fun u => ((β u).order_mem_orderedSteps (h.pointwise u)).1

/-- On a finitely supported step field the ordered marked tree is had with nothing handed in: the field is
orderable by instance search. -/
noncomputable def StepField.markedTreeOfOrderable' [LinearOrder Position]
    (β : StepField ℕ Position)
    [h : StepField.IsFinitelySupported β] : MarkedTree ℕ Position :=
  β.markedTreeOfOrderable inferInstance

/-- The marked tree of an orderable walk, one tree for each initial ancestor. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTreeOfOrderable
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (h : β.IsOrderable) :
    UlamHarris.RootIndexed.MarkedTree Root ℕ Position :=
  fun r => markedTreeOfStep
    (StepField.map d
      (fun u => (β.step r u).order ((h.pointwise r).pointwise u)))
    (fun u => by
      intro i j hij hi
      have hi' : (β.step r u).order ((h.pointwise r).pointwise u) i = none := by
        simpa [StepField.map, Step.map] using hi
      have hj' := (((β.step r u).order_mem_orderedSteps
        ((h.pointwise r).pointwise u)).1 i j hij hi')
      simpa [StepField.map, Step.map] using hj')

/-- On a finitely supported walk the ordered marked tree is had with nothing handed in. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTreeOfOrderable'
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position)
    [h : RootIndexed.BranchingWalk.IsFinitelySupported β] :
    UlamHarris.RootIndexed.MarkedTree Root ℕ Position :=
  β.positionedMarkedTreeOfOrderable d inferInstance

end AddCommGroup

end General

end Branching

end Combinatorics

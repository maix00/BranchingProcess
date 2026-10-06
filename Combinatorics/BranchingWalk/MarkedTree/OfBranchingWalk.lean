/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.MarkedTree.Equivalence
public import Combinatorics.BranchingWalk.MarkedTree.Ordering
public import Combinatorics.BranchingWalk.Basic.Orderable
public import Combinatorics.BranchingWalk.Basic.DisplacementMap
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.UlamHarris.MarkedTree.Basic

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

@[expose] public section

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
  fun r => (β.step r).positionedMarkedTreeOfClosable d (h r)

/-- The positioned ordered realization of a branching walk, one tree for each
initial ancestor. Each node reads the offspring step at the old address reached
by the recursively transported path, so descendant subtrees move with their
parents. The displacement map is applied only after ordering the original
edge marks. -/
noncomputable def RootIndexed.BranchingWalk.positionedMarkedTreeOfOrderable
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (h : β.IsOrderable) :
    UlamHarris.RootIndexed.MarkedTree Root ℕ Position :=
  fun r => (β.step r).markedTreeOfOrderingMap (h.pointwise r) d

/-- Carrier membership in the positioned ordered tree is survival of the
address obtained by recursively applying the orderings at its old ancestors. -/
@[simp] theorem RootIndexed.BranchingWalk.mem_positionedMarkedTreeOfOrderable_iff
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (h : β.IsOrderable) (r : Root)
    (u : TreeNode ℕ) :
    u ∈ (β.positionedMarkedTreeOfOrderable d h r).tree.carrier ↔
      surviveAlong (β.step r) []
        (StepField.orderingAddress (β.step r) (h.pointwise r) u) := by
  change surviveAlong
      (StepField.map d (StepField.orderingField (β.step r) (h.pointwise r))) [] u ↔ _
  rw [surviveAlong_map_iff]
  exact StepField.surviveAlong_orderingAddress_iff (β.step r) (h.pointwise r) u

/-- Each old realized particle has a unique address in the positioned ordered
tree of the same root. Different initial ancestors are handled independently. -/
theorem RootIndexed.BranchingWalk.existsUnique_positionedOrderingAddress
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (h : β.IsOrderable) (r : Root)
    {u : TreeNode ℕ} (hu : surviveAlong (β.step r) [] u) :
    ∃! v, v ∈ (β.positionedMarkedTreeOfOrderable d h r).tree.carrier ∧
      StepField.orderingAddress (β.step r) (h.pointwise r) v = u := by
  obtain ⟨v, hv, haddr⟩ := StepField.exists_orderingAddress_preimage
    (β.step r) (h.pointwise r) hu
  have hvRaw := (StepField.surviveAlong_orderingAddress_iff
    (β.step r) (h.pointwise r) v).mp hv
  have hv' : v ∈ (β.positionedMarkedTreeOfOrderable d h r).tree.carrier :=
    StepField.mem_markedTreeOfOrderingMap_iff
      (β.step r) (h.pointwise r) d v |>.2 hvRaw
  refine ⟨v, ⟨hv', haddr⟩, ?_⟩
  intro w hw
  exact (StepField.injective_orderingAddress (β.step r) (h.pointwise r))
    (hw.2.trans haddr.symm)

/-- Node marks in the positioned ordered tree are the old accumulated
positions read at the recursively transported genealogical address. -/
theorem RootIndexed.BranchingWalk.positionedMarkedTreeOfOrderable_mark
    {Mark : Type*} [LinearOrder Mark]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (h : β.IsOrderable) (r : Root)
    (u : TreeNode ℕ)
    (hu : u ∈ (β.positionedMarkedTreeOfOrderable d h r).tree.carrier) :
    (β.positionedMarkedTreeOfOrderable d h r).mark u hu =
      displaceWith d (β.step r) []
        (StepField.orderingAddress (β.step r) (h.pointwise r) u) := by
  exact StepField.markedTreeOfOrderingMap_mark
    (β.step r) (h.pointwise r) d u hu

/-- The offspring point measure at an ordered parent is the pushforward by
`d` of the raw point measure at its corresponding old parent. -/
theorem RootIndexed.BranchingWalk.positionedOrderedStepPointMeasure
    {Mark : Type*} [LinearOrder Mark]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (β : RootIndexed.BranchingWalk Root ℕ Mark Position)
    (d : Mark → Position) (hd : Measurable d) (h : β.IsOrderable)
    (r : Root) (u : TreeNode ℕ)
    (hu : u ∈ (β.positionedMarkedTreeOfOrderable d h r).tree.carrier) :
    stepPointMeasure
        (stepOfMarkedTree (β.positionedMarkedTreeOfOrderable d h r) u) =
      (stepPointMeasure (β.step r
        (StepField.orderingAddress (β.step r) (h.pointwise r) u))).map d := by
  have huOrdered : surviveAlong
      (StepField.map d (StepField.orderingField (β.step r) (h.pointwise r))) [] u := hu
  have hstep : stepOfMarkedTree
      ((β.step r).markedTreeOfOrderingMap (h.pointwise r) d) u =
      StepField.map d (StepField.orderingField (β.step r) (h.pointwise r)) u :=
    stepOfMarkedTree_markedTreeOfStep_of_realized
      (StepField.map d (StepField.orderingField (β.step r) (h.pointwise r)))
      (fun v => by
        intro i j hij hi
        have hi' : StepField.orderingField (β.step r) (h.pointwise r) v i = none := by
          simpa [StepField.map, Step.map] using hi
        have hj' := (StepField.IsSiblingClosed_orderingField
          (β.step r) (h.pointwise r) v) i j hij hi'
        simpa [StepField.map, Step.map] using hj') huOrdered
  rw [show β.positionedMarkedTreeOfOrderable d h r =
      (β.step r).markedTreeOfOrderingMap (h.pointwise r) d from rfl, hstep]
  exact StepField.stepPointMeasure_orderingField_map
    (β.step r) (h.pointwise r) d hd u

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

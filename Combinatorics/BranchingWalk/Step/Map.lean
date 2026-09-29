module

public import Combinatorics.Branching.Basic

/-!
# Mapping branching-step marks

A branching step has two independent pieces of information: which slots are
present and the mark carried by each present slot. `Step.map` changes only the
marks. The survival set, paths, and genealogy are therefore invariant.

This is the common abstraction behind spatial transformations and forgetting
all spatial marks. The latter maps every mark to `PUnit`; it is not a separate
branching-tree representation.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Map the mark of every present child, preserving absent slots. -/
def Step.map {ι X Y : Type*} (f : X → Y) (ξ : Step ι X) : Step ι Y :=
  fun i => (ξ i).map f

@[simp] theorem Step.map_apply {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) (i : ι) :
    ξ.map f i = (ξ i).map f := rfl

@[simp] theorem Step.map_id {ι X : Type*} (ξ : Step ι X) :
    ξ.map id = ξ := by
  funext i
  simp [Step.map]

@[simp] theorem Step.map_map {ι X Y Z : Type*} (g : Y → Z) (f : X → Y)
    (ξ : Step ι X) :
    (ξ.map f).map g = ξ.map (g ∘ f) := by
  funext i
  simp [Step.map]

@[simp] theorem survive_map_iff {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) (i : ι) :
    survive (ξ.map f) i ↔ survive ξ i := by
  cases h : ξ i <;> simp [Step.map, survive, h]

@[simp] theorem Step.support_map {ι X Y : Type*} (f : X → Y)
    (ξ : Step ι X) :
    support (ξ.map f) = support ξ := by
  ext i
  simp [support]

/-- Forget every child mark while retaining exactly the child slots. -/
def Step.forgetMark {ι X : Type*} (ξ : Step ι X) : Step ι PUnit.{1} :=
  ξ.map (fun _ => PUnit.unit.{1})

@[simp] theorem survive_forgetMark_iff {ι X : Type*} (ξ : Step ι X) (i : ι) :
    survive ξ.forgetMark i ↔ survive ξ i :=
  survive_map_iff _ _ _

/-- Map every step in a deterministic field through the same mark map. -/
def StepField.map {α X Y : Type*} (f : X → Y)
    (β : StepField α X) : StepField α Y :=
  fun u => (β u).map f

@[simp] theorem StepField.map_apply {α X Y : Type*} (f : X → Y)
    (β : StepField α X) (u : TreeNode α) :
    β.map f u = (β u).map f := rfl

@[simp] theorem StepField.map_id {α X : Type*} (β : StepField α X) :
    β.map id = β := by
  funext u
  exact Step.map_id (β u)

@[simp] theorem StepField.map_map {α X Y Z : Type*}
    (g : Y → Z) (f : X → Y) (β : StepField α X) :
    (β.map f).map g = β.map (g ∘ f) := by
  funext u
  exact Step.map_map g f (β u)

@[simp] theorem surviveAlong_map_iff {α X Y : Type*} (f : X → Y)
    (β : StepField α X) (v p : TreeNode α) :
    surviveAlong (β.map f) v p ↔ surviveAlong β v p := by
  induction p generalizing v with
  | nil => simp [surviveAlong]
  | cons i p ih => simp [surviveAlong, ih]

/-- Forget every mark in a step field while retaining its genealogy. -/
def StepField.forgetMarks {α X : Type*} (β : StepField α X) :
    StepField α PUnit.{1} :=
  β.map (fun _ => PUnit.unit.{1})

/-- Map the spatial marks and initial positions of a root-indexed branching
walk. Since mapping preserves survival, the same parent-closure proof applies. -/
def RootIndexed.BranchingWalk.map {Root α X Y : Type*}
    (f : X → Y) (β : RootIndexed.BranchingWalk Root α X X) :
    RootIndexed.BranchingWalk Root α Y Y where
  step r := (β.step r).map f
  initial r := f (β.initial r)
  parentClosed r u v h :=
    (surviveAlong_map_iff f (β.step r) [] u).2
      (β.parentClosed r u v
        ((surviveAlong_map_iff f (β.step r) [] (u ++ v)).1 h))

/-- Forget all spatial marks of a branching walk. The result is the unit-marked
special case carrying only its genealogical branching structure. -/
def RootIndexed.BranchingWalk.toBranching
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    RootIndexed.Process Root α where
  step r := (β.step r).forgetMarks
  initial _ := PUnit.unit
  parentClosed r u v h :=
    (surviveAlong_map_iff _ (β.step r) [] u).2
      (β.parentClosed r u v
        ((surviveAlong_map_iff _ (β.step r) [] (u ++ v)).1 h))

@[simp] theorem RootIndexed.BranchingWalk.surviveAlong_toBranching_iff
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (r : Root) (v p : TreeNode α) :
    surviveAlong (β.toBranching.step r) v p ↔
      surviveAlong (β.step r) v p :=
  surviveAlong_map_iff _ _ _ _

end Combinatorics.Branching

end

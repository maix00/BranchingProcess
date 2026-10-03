module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.Map

/-!
# Mapping branching-walk marks and positions

This file maps a complete step field or changes one coordinate of a root-
indexed branching walk. The deterministic one-step mapping API is in
`Combinatorics/BranchingWalk/Step/Map.lean`.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Map the mark of every step in a deterministic field. -/
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

/-- Change only the child marks of a root-indexed branching walk. -/
def RootIndexed.BranchingWalk.mapMarks {Root α Mark Mark' Position : Type*}
    (f : Mark → Mark')
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    RootIndexed.BranchingWalk Root α Mark' Position where
  step r := (β.step r).map f
  initial := β.initial

/-- Change only the initial positions of a root-indexed branching walk. -/
def RootIndexed.BranchingWalk.mapInitial {Root α Mark Position Position' : Type*}
    (f : Position → Position')
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    RootIndexed.BranchingWalk Root α Mark Position' where
  step := β.step
  initial r := f (β.initial r)

/-- Map marks and initial positions by the same function. -/
def RootIndexed.BranchingWalk.map {Root α X Y : Type*}
    (f : X → Y) (β : RootIndexed.BranchingWalk Root α X X) :
    RootIndexed.BranchingWalk Root α Y Y :=
  (β.mapMarks f).mapInitial f

@[simp] theorem RootIndexed.BranchingWalk.mapMarks_step
    {Root α Mark Mark' Position : Type*} (f : Mark → Mark')
    (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root) :
    (β.mapMarks f).step r = (β.step r).map f := rfl

@[simp] theorem RootIndexed.BranchingWalk.mapMarks_initial
    {Root α Mark Mark' Position : Type*} (f : Mark → Mark')
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    (β.mapMarks f).initial = β.initial := rfl

@[simp] theorem RootIndexed.BranchingWalk.mapInitial_step
    {Root α Mark Position Position' : Type*} (f : Position → Position')
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    (β.mapInitial f).step = β.step := rfl

@[simp] theorem RootIndexed.BranchingWalk.mapInitial_initial
    {Root α Mark Position Position' : Type*} (f : Position → Position')
    (β : RootIndexed.BranchingWalk Root α Mark Position) (r : Root) :
    (β.mapInitial f).initial r = f (β.initial r) := rfl

end Combinatorics.Branching

end

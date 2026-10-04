/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.StepField

/-!
# Mapping realized branching walks

Pointwise maps of deterministic step fields live in
`Combinatorics/BranchingWalk/StepField.lean`. This file maps realized
root-indexed branching walks and records the resulting survival relation.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

@[simp] theorem surviveAlong_map_iff {α X Y : Type*} (f : X → Y)
    (β : StepField α X) (v p : TreeNode α) :
    surviveAlong (β.map f) v p ↔ surviveAlong β v p := by
  induction p generalizing v with
  | nil => simp [surviveAlong]
  | cons i p ih => simp [surviveAlong, ih]

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

/-- Mapping child marks is measurable on root-indexed branching walks. -/
theorem RootIndexed.BranchingWalk.mapMarks_measurable
    {Root α Mark Mark' Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Mark'] [MeasurableSpace Position]
    {f : Mark → Mark'} (hf : Measurable f) :
    Measurable (RootIndexed.BranchingWalk.mapMarks (Root := Root)
      (α := α) (Position := Position) f) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change MeasurableSet
    ((fun β : RootIndexed.BranchingWalk Root α Mark Position =>
      ((β.mapMarks f).step, (β.mapMarks f).initial)) ⁻¹' t)
  have hpair : Measurable
      (fun β : RootIndexed.BranchingWalk Root α Mark Position =>
        ((β.mapMarks f).step, (β.mapMarks f).initial)) := by
    change Measurable (fun β :
        RootIndexed.BranchingWalk Root α Mark Position =>
      ((fun (r : Root) => StepField.map f (β.step r)), β.initial))
    have hwalk : Measurable (fun β :
        RootIndexed.BranchingWalk Root α Mark Position =>
        (β.step, β.initial)) := Measurable.of_comap_le le_rfl
    have hstep : Measurable (fun β :
        RootIndexed.BranchingWalk Root α Mark Position =>
        fun (r : Root) => StepField.map f (β.step r)) := by
      apply measurable_pi_iff.mpr
      intro r
      exact (StepField.map_measurable hf).comp
        ((measurable_pi_apply r).comp (measurable_fst.comp hwalk))
    exact hstep.prodMk (measurable_snd.comp hwalk)
  exact hpair ht

/-- Changing initial positions is measurable on root-indexed branching
walks. -/
theorem RootIndexed.BranchingWalk.mapInitial_measurable
    {Root α Mark Position Position' : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace Position'] {f : Position → Position'}
    (hf : Measurable f) :
    Measurable (RootIndexed.BranchingWalk.mapInitial (Root := Root)
      (α := α) (Mark := Mark) f) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  change MeasurableSet
    ((fun β : RootIndexed.BranchingWalk Root α Mark Position =>
      ((β.mapInitial f).step, (β.mapInitial f).initial)) ⁻¹' t)
  have hwalk : Measurable (fun β :
      RootIndexed.BranchingWalk Root α Mark Position =>
      (β.step, β.initial)) := Measurable.of_comap_le le_rfl
  have hpair : Measurable
      (fun β : RootIndexed.BranchingWalk Root α Mark Position =>
        (β.step, fun r => f (β.initial r))) := by
    have hinitial : Measurable (fun β :
        RootIndexed.BranchingWalk Root α Mark Position =>
        fun r => f (β.initial r)) := by
      apply measurable_pi_iff.mpr
      intro r
      exact hf.comp ((measurable_pi_apply r).comp
        (measurable_snd.comp hwalk))
    exact (measurable_fst.comp hwalk).prodMk hinitial
  exact hpair ht

end Combinatorics.Branching

end

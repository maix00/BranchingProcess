/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Mapping branching-step marks

A branching step records which slots are present and the marks carried by
those children. `Step.map` changes only the marks, so the survival set is
invariant. Maps of complete step fields live in
`Combinatorics/BranchingWalk/StepField.lean`; maps of branching walks live in
`Combinatorics/BranchingWalk/Basic/Map.lean`.

The public API is:

- `Step.map f ξ` applies `f` to each present mark and preserves absent slots;
  `Step.map_apply`, `Step.map_id`, and `Step.map_map` give its coordinate,
  identity, and composition laws.
- `survive_map_iff` and `Step.support_map` state that relabeling marks
  preserves the set of present slots.
- `Step.value'_map` states that a zero-preserving mark map commutes with the
  zero-defaulted slot reading: `value' (ξ.map f) i = f (value' ξ i)`.
- `Step.map_measurable` proves measurability when `f` is measurable.
- `Step.forgetMark` replaces every present mark by `PUnit.unit`, and
  `survive_forgetMark_iff` records preservation of survival.
-/

@[expose] public section

namespace Combinatorics.Branching

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

/-- A zero-preserving mark map commutes with the zero-defaulted reading of a
slot. -/
theorem Step.value'_map {ι X Y : Type*} [Zero X] [Zero Y]
    (f : X → Y) (hf : f 0 = 0) (ξ : Step ι X) (i : ι) :
    value' (ξ.map f) i = f (value' ξ i) := by
  cases h : ξ i with
  | none => simp [value', Step.map, h, hf]
  | some x => simp [value', Step.map, h]

/-- Mapping the marks coordinatewise is measurable when the mark map is
measurable. -/
theorem Step.map_measurable {ι X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : Measurable f) :
    Measurable (Step.map (ι := ι) f) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_option_map hf).comp (measurable_pi_apply i)

/-- Forget every child mark while retaining exactly the child slots. -/
def Step.forgetMark {ι X : Type*} (ξ : Step ι X) : Step ι PUnit.{1} :=
  ξ.map (fun _ => PUnit.unit.{1})

@[simp] theorem survive_forgetMark_iff {ι X : Type*} (ξ : Step ι X) (i : ι) :
    survive ξ.forgetMark i ↔ survive ξ i :=
  survive_map_iff _ _ _

end Combinatorics.Branching

end

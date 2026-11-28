/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic

/-!
# Selecting whole offspring families

## Public declarations

In `Combinatorics.Branching.Step`:

* `selectFamily accepted ξ` retains `ξ` when `ξ ∈ accepted` and otherwise
  gives the empty offspring configuration, at every child slot.
* `selectFamily_of_mem` and `selectFamily_of_notMem` give those two cases.
* `selectFamily_measurable` proves measurability for a measurable family event.

The rule tests the whole family, rather than individual child marks; all
siblings are retained or removed together. There is no ordering, finite
population or probabilistic assumption.
-/

@[expose] public section
namespace Combinatorics.Branching.Step
open MeasureTheory
open scoped Classical

/-- Retain an accepted offspring family and remove every child otherwise. -/
noncomputable def selectFamily {ι X : Type*} (accepted : Set (Step ι X))
    (ξ : Step ι X) : Step ι X :=
  if ξ ∈ accepted then ξ else fun _ => none

@[simp] theorem selectFamily_of_mem {ι X : Type*} {accepted : Set (Step ι X)}
    {ξ : Step ι X} (hξ : ξ ∈ accepted) : selectFamily accepted ξ = ξ := by
  simp [selectFamily, hξ]

@[simp] theorem selectFamily_of_notMem {ι X : Type*} {accepted : Set (Step ι X)}
    {ξ : Step ι X} (hξ : ξ ∉ accepted) : selectFamily accepted ξ = fun _ => none := by
  simp [selectFamily, hξ]

theorem selectFamily_measurable {ι X : Type*} [MeasurableSpace X]
    {accepted : Set (Step ι X)} (ha : MeasurableSet accepted) :
    Measurable (selectFamily accepted) := measurable_id.ite ha measurable_const

end Combinatorics.Branching.Step

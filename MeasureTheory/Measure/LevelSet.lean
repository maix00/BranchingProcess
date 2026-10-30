/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Null-measure fibers over uncountable sets

## Public declarations

* `MeasureTheory.exists_measure_zero_fiber_of_not_countable`: if `g : α → β` is measurable,
  `μ` is an s-finite measure, and `S ⊆ β` is uncountable, then some `y ∈ S` has a
  null fiber `{x | g x = y}`. The codomain only needs measurable singletons.

The result follows from Mathlib's
`Measure.countable_meas_level_set_pos`, which says that only countably many
measurable fibers can have positive measure.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

/-- Every uncountable subset of a measurable codomain contains a level whose fiber under a
measurable map has measure zero. -/
theorem exists_measure_zero_fiber_of_not_countable {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β] {μ : Measure α} [SFinite μ]
    {g : α → β} (hg : Measurable g) {S : Set β} (hS : ¬ S.Countable) :
    ∃ y ∈ S, μ {x | g x = y} = 0 := by
  have hbad : Set.Countable {y : β | 0 < μ {x : α | g x = y}} :=
    Measure.countable_meas_level_set_pos hg
  have hnotSubset : ¬ S ⊆ {y : β | 0 < μ {x : α | g x = y}} := by
    intro hsubset
    exact hS (hbad.mono hsubset)
  obtain ⟨y, hy, hybad⟩ := Set.not_subset.mp hnotSubset
  refine ⟨y, hy, ?_⟩
  exact le_antisymm (not_lt.mp hybad) zero_le

end MeasureTheory

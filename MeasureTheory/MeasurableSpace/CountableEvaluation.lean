/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable evaluation at a countable-range selector

For a field `F : Ω → I → X` and a selector `s : Ω → I`, the evaluation
`ω ↦ F ω (s ω)` is measurable when every coordinate in the range of `s` is
measurable, each selector fiber is measurable, and the range of `s` is
countable. The index type needs no measurable-space structure.

## Public declarations

* `measurable_of_countable_range_of_fibers` proves that `s : Ω → I` is
  measurable when its actual range is countable and each fiber
  `{ω | s ω = i}` is measurable.
* `Measurable.eval_of_countable_range` proves measurability of the field
  evaluation `ω ↦ F ω (s ω)` when the selected coordinates and selector
  fibers are measurable and the actual range of `s` is countable.
-/

@[expose] public section

/-- A function with countable actual range is measurable when every fiber
is measurable. -/
theorem measurable_of_countable_range_of_fibers
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (chosen : Ω → I)
    (hfiber : ∀ i, MeasurableSet {ω | chosen ω = i})
    (hcount : (Set.range chosen).Countable) :
    Measurable chosen := by
  intro t ht
  change MeasurableSet {ω | chosen ω ∈ t}
  let R : Set I := Set.range chosen
  let _ : Countable R := Set.countable_coe_iff.mpr hcount
  have hpreimage : {ω | chosen ω ∈ t} =
      ⋃ i : {i : R // i.1 ∈ t}, {ω | chosen ω = i.1.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨⟨⟨chosen ω, Set.mem_range_self ω⟩, h⟩, rfl⟩
    · rintro ⟨i, hi⟩
      simpa [hi] using i.2
  rw [hpreimage]
  exact MeasurableSet.iUnion fun i => hfiber i.1.1

/-- Evaluation of a measurable field at a selector with countable range is
measurable when the selector fibers and the coordinates actually selected
are measurable. No measurable-space structure on the index type is needed. -/
theorem Measurable.eval_of_countable_range
    {Ω I X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (field : Ω → I → X) (chosen : Ω → I)
    (hcoordinate : ∀ i, i ∈ Set.range chosen →
      Measurable (fun ω => field ω i))
    (hfiber : ∀ i, i ∈ Set.range chosen → MeasurableSet {ω | chosen ω = i})
    (hcount : (Set.range chosen).Countable) :
    Measurable (fun ω => field ω (chosen ω)) := by
  let S : Set I := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro t ht
  change MeasurableSet {ω | field ω (chosen ω) ∈ t}
  have hpreimage :
      {ω | field ω (chosen ω) ∈ t} =
        ⋃ i : S, {ω | chosen ω = i.1} ∩
          {ω | field ω i.1 ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨i, hi, hfield⟩
      simpa [hi] using hfield
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro i
  exact (hfiber i.1 i.2).inter ((hcoordinate i.1 i.2) ht)

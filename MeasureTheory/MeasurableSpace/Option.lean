/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable options

`Option X` carries the disjoint-union measurable structure used for partial
random maps: `some x` is an ordinary value and `none` is a cemetery value.

## Public declarations

The measurable structure on options is induced by `some`; measurable maps
remain measurable after mapping through `Option.map`:

\[
\mathcal M_{\operatorname{Option}(X)}
=\operatorname{map}(\operatorname{some})\,\mathcal M_X,
\qquad
f\text{ measurable}\Longrightarrow
\bigl(o\mapsto\operatorname{map}(f,o)\bigr)\text{ measurable}.
\]

* `MeasureTheory.optionMeasurableSpace X` is the measurable space induced by
  `some : X → Option X`.
* `MeasureTheory.measurableSet_option_none` and
  `MeasureTheory.measurableSet_option_some_image` show that `{none}` and the
  image `some '' s` of a measurable set are measurable.
* `MeasureTheory.measurable_option_some` and
  `MeasureTheory.measurableEmbedding_option_some` state that `some` is a
  measurable embedding. `MeasureTheory.measurable_option_map` proves
  measurability of `Option.map f` when `f` is measurable.
* `MeasureTheory.measurable_optionGetD d` states that
  `o ↦ o.getD d` is measurable, and
  `MeasureTheory.measurable_option_elim none hsome` states that
  `o ↦ o.elim none some` is measurable when `some` is measurable.
* `MeasureTheory.measurableSet_option_isSome` states that
  `{o : Option X | o.isSome}` is measurable.
-/

public section

namespace MeasureTheory

/-- The disjoint-union measurable structure on an optional value. -/
instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) :=
  MeasurableSpace.map (some : X → Option X) inferInstance

theorem measurableSet_option_none {X : Type*} [MeasurableSpace X] :
    MeasurableSet ({none} : Set (Option X)) := by
  change MeasurableSet (some ⁻¹' ({none} : Set (Option X)))
  rw [show (some ⁻¹' ({none} : Set (Option X))) = (∅ : Set X) by
    ext x
    simp]
  exact MeasurableSet.empty

theorem measurableSet_option_some_image {X : Type*} [MeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (some '' s) := by
  change MeasurableSet (some ⁻¹' (some '' s))
  rwa [Set.preimage_image_eq s (Option.some_injective X)]

theorem measurable_option_some {X : Type*} [MeasurableSpace X] :
    Measurable (some : X → Option X) := fun _s hs => hs

theorem measurableEmbedding_option_some {X : Type*} [MeasurableSpace X] :
    MeasurableEmbedding (some : X → Option X) :=
  ⟨Option.some_injective X, measurable_option_some,
    fun _s hs => measurableSet_option_some_image hs⟩

theorem measurable_option_map {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) :
    Measurable (Option.map f) := by
  intro s hs
  change MeasurableSet (f ⁻¹' (some ⁻¹' s))
  exact hf hs

theorem measurable_optionGetD {X : Type*} [MeasurableSpace X] (d : X) :
    Measurable (fun o : Option X => o.getD d) := by
  intro s hs
  change MeasurableSet (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s))
  rw [show (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s)) = s by
    ext x
    simp]
  exact hs

/-- Eliminating an optional measurable value is measurable whenever the
present branch is measurable. -/
theorem measurable_option_elim {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (none : Y) {some : X → Y} (hsome : Measurable some) :
    Measurable (fun o : Option X => o.elim none some) := by
  intro s hs
  change MeasurableSet (some ⁻¹' s)
  exact hsome hs

/-- Presence of an optional value is a measurable event. -/
theorem measurableSet_option_isSome {X : Type*} [MeasurableSpace X] :
    MeasurableSet {o : Option X | o.isSome} := by
  rw [show {o : Option X | o.isSome} = some '' (Set.univ : Set X) by
    ext o
    cases o <;> simp]
  exact measurableSet_option_some_image MeasurableSet.univ

end MeasureTheory

end

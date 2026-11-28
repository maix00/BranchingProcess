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
* `MeasureTheory.optionMeasurableSingletonClass`: measurable singletons in `X`
  give measurable singletons `{none}` and `{some x}` in `Option X`.
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
* `Measurable.option_elim` allows the absent value and the present branch
  to depend measurably on a parameter: if $o$, $g$ and $(w,e)\mapsto f(w,e)$
  are measurable, then $w\mapsto o(w).\mathrm{elim}(g(w),f(w,\cdot))$ is measurable.
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

/-- Optional values have measurable singletons whenever their value type does. -/
instance optionMeasurableSingletonClass {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] : MeasurableSingletonClass (Option X) where
  measurableSet_singleton o := by
    cases o with
    | none => exact measurableSet_option_none
    | some x =>
      convert measurableSet_option_some_image (measurableSet_singleton x) using 1
      ext o
      simp

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

/-- Eliminate a random optional value with measurably varying branches. -/
theorem Measurable.option_elim {Ω X Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {o : Ω → Option X} {g : Ω → Y} {f : Ω → X → Y}
    (ho : Measurable o) (hg : Measurable g)
    (hf : Measurable (fun p : Ω × X => f p.1 p.2)) :
    Measurable (fun w => (o w).elim (g w) (f w)) := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    have hsome := hf.comp
      (measurable_id.prodMk ((MeasureTheory.measurable_optionGetD x).comp ho))
    have hset := MeasureTheory.measurableSet_option_isSome.preimage ho
    have hpiece : Measurable
        (Set.piecewise {w | (o w).isSome} (fun w => f w ((o w).getD x)) g) :=
      hsome.piecewise hset hg
    convert hpiece using 1
    ext w
    cases h : o w <;> simp [h, Set.piecewise]
  · have heq : o = fun _ => none := by
      funext w
      cases h : o w with
      | none => rfl
      | some x => exact (hX ⟨x⟩).elim
    simpa [heq] using hg

end

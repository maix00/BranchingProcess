module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable options

`Option X` carries the disjoint-union measurable structure used for partial
random maps: `some x` is an ordinary value and `none` is a cemetery value.
-/

public section

open MeasureTheory

/-- The disjoint-union measurable structure on an optional value. -/
instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) where
  MeasurableSet' s := MeasurableSet (some ⁻¹' s)
  measurableSet_empty := by
    rw [show (some ⁻¹' (∅ : Set (Option X))) = (∅ : Set X) by
      ext x
      simp]
    exact MeasurableSet.empty
  measurableSet_compl _s hs := by
    simpa [Set.preimage_compl] using hs.compl
  measurableSet_iUnion _f hf := by
    simpa [Set.preimage_iUnion] using MeasurableSet.iUnion hf

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

end

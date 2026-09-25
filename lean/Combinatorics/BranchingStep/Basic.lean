import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued child-slot encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  Absence is a first-class value, so a slot field
may have no children at all.

The file carries the primitive type, its measurable structure, and the
presence predicate. The order conditions on present slots are in
`Prefix.lean`, the increment and support calculus in `Increment.lean`, and the
real-line specialization in `Slot/Basic.lean`.
-/

open MeasureTheory
open Classical

/-- A branching step: one optional child mark per slot label. -/
abbrev BranchingStep (ι X : Type*) := ι → Option X

namespace BranchingStep


/-! `Option` is the presence/absence wrapper. Its measurable structure is the
    disjoint-union one: a set is measurable exactly when its `some`-part is a
    measurable subset of `X`. This makes `some` measurable, `none` a measurable
    point, and `getD d` measurable — the three facts the slot calculus needs.
    The discrete structure would make `some` non-measurable and would therefore
    destroy the measurability of a step constructed from a measure. -/
instance branchingStepOptionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) where
  MeasurableSet' s := MeasurableSet (some ⁻¹' s)
  measurableSet_empty := by
    rw [show (some ⁻¹' (∅ : Set (Option X))) = (∅ : Set X) by
      ext x
      simp]
    exact MeasurableSet.empty
  measurableSet_compl s hs := by
    simp [Set.preimage_compl, hs]
  measurableSet_iUnion f hf := by
    simpa [Set.preimage_iUnion] using MeasurableSet.iUnion hf

/-- `none` is a measurable point of the disjoint-union structure. -/
theorem measurableSet_option_none {X : Type*} [MeasurableSpace X] :
    MeasurableSet ({none} : Set (Option X)) := by
  change MeasurableSet (some ⁻¹' ({none} : Set (Option X)))
  rw [show (some ⁻¹' ({none} : Set (Option X))) = (∅ : Set X) by
    ext x
    simp]
  exact MeasurableSet.empty

/-- The image of a measurable set under `some` is measurable. -/
theorem measurableSet_option_some_image {X : Type*} [MeasurableSpace X]
    {s : Set X} (hs : MeasurableSet s) :
    MeasurableSet (some '' s) := by
  change MeasurableSet (some ⁻¹' (some '' s))
  rwa [Set.preimage_image_eq s (Option.some_injective X)]

/-- The presence constructor is measurable. -/
theorem measurable_option_some {X : Type*} [MeasurableSpace X] :
    Measurable (some : X → Option X) := by
  intro s hs
  exact hs

/-- Substituting a default value on the absent slot is measurable. -/
theorem measurable_optionGetD {X : Type*} [MeasurableSpace X] (d : X) :
    Measurable (fun o : Option X => o.getD d) := by
  intro s hs
  change MeasurableSet (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s))
  rw [show (some ⁻¹' ((fun o : Option X => o.getD d) ⁻¹' s)) = s by
    ext x
    simp]
  exact hs

/-! The measurable structure on a branching step is the coordinate-wise
    measurable structure.  This belongs to the abstract step layer; concrete
    point-process realizations may add further structure later. -/
instance branchingStepMeasurableSpace {ι X : Type*} [MeasurableSpace X] :
    MeasurableSpace (BranchingStep ι X) := MeasurableSpace.pi

def branchingStepPresent {ι X : Type*}
    (ξ : BranchingStep ι X) (i : ι) : Prop := ∃ x, ξ i = some x

theorem branchingStepPresent_iff_ne_none {ι X : Type*}
    (ξ : BranchingStep ι X) (i : ι) :
    branchingStepPresent ξ i ↔ ξ i ≠ none := by
  cases h : ξ i with
  | none => simp [branchingStepPresent, h]
  | some x => simp [branchingStepPresent, h]

theorem branchingStepPresent_measurableSet
    {ι X : Type*} [MeasurableSpace X] (i : ι) :
    MeasurableSet {ξ : BranchingStep ι X | branchingStepPresent ξ i} := by
  rw [show {ξ : BranchingStep ι X | branchingStepPresent ξ i} =
      (fun ξ : BranchingStep ι X => ξ i) ⁻¹' ({none}ᶜ) by
        ext ξ
        simp [branchingStepPresent_iff_ne_none]]
  exact (measurable_pi_apply i) measurableSet_option_none.compl

theorem branchingStep_value_of_present
    {ι X : Type*} (ξ : BranchingStep ι X) {i : ι}
    (hi : branchingStepPresent ξ i) : ∃ x, ξ i = some x := hi

end BranchingStep

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Option-valued child-slot encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  Absence is a first-class value, so a slot field
may have no children at all.

The file carries the primitive type, its measurable structure, the presence
predicate, the support of a step, the zero-defaulted slot reading, and the
`ℕ`-labelled specializations `NatStep` and `NatRealStep`.  A slot is read
directly as `ξ i`; the zero-defaulted reading `value' ξ i` is separate because
it needs a `Zero X` instance and is not part of the type of a step.  The
relation layer is in `Relation/Basic.lean`, the ordered layer in
`Ordered.lean`, the slot vocabulary in `Step/Measurability.lean`,
the realized-child predicate in `Displace/Node.lean`, the displacements in
`Displace/`, and the realized and marked trees in `Tree/`.
-/

open MeasureTheory
open Classical

namespace MeasureTheory

namespace BranchingWalk

/-- A branching step: one optional child mark per slot label. -/
abbrev Step (ι X : Type*) := ι → Option X

/-- The zero-defaulted mark of a slot. -/
def value' {ι X : Type*} [Zero X] (ξ : Step ι X) (i : ι) : X :=
  (ξ i).getD 0

theorem value'_eq_getD {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) :
    value' ξ i = (ξ i).getD 0 := rfl

theorem value'_none {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) (h : ξ i = none) :
    value' ξ i = 0 := by
  simp [value', h]

theorem value'_some {ι X : Type*} [Zero X]
    (ξ : Step ι X) (i : ι) (x : X) (h : ξ i = some x) :
    value' ξ i = x := by
  simp [value', h]

/-- A branching step whose slots are labelled by `ℕ`: the paper's optional
enumeration of the children of one node, with arbitrary slot values. -/
abbrev NatStep (X : Type*) := Step ℕ X

/-- The paper's branching step: `ℕ`-labelled optional children at real
displacements. -/
abbrev NatRealStep := NatStep ℝ

/-! `Option` is the presence/absence wrapper. Its measurable structure is the
    disjoint-union one: a set is measurable exactly when its `some`-part is a
    measurable subset of `X`. This makes `some` measurable, `none` a measurable
    point, and `getD d` measurable — the three facts the slot calculus needs.
    The discrete structure would make `some` non-measurable and would therefore
    destroy the measurability of a step constructed from a measure. -/
instance stepOptionMeasurableSpace {X : Type*} [MeasurableSpace X] :
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
instance stepMeasurableSpace {ι X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Step ι X) := MeasurableSpace.pi

theorem value'_measurable
    {ι X : Type*} [MeasurableSpace X] [Zero X] (i : ι) :
    Measurable (fun ξ : Step ι X => value' ξ i) := by
  rw [show (fun ξ : Step ι X => value' ξ i) =
      fun ξ : Step ι X => (ξ i).getD (0 : X) by
        funext ξ; exact value'_eq_getD ξ i]
  exact (measurable_optionGetD (0 : X)).comp (measurable_pi_apply i)

def present {ι X : Type*}
    (ξ : Step ι X) (i : ι) : Prop := ∃ x, ξ i = some x

theorem present_iff_ne_none {ι X : Type*}
    (ξ : Step ι X) (i : ι) :
    present ξ i ↔ ξ i ≠ none := by
  cases h : ξ i with
  | none => simp [present, h]
  | some x => simp [present, h]

theorem present_measurableSet
    {ι X : Type*} [MeasurableSpace X] (i : ι) :
    MeasurableSet {ξ : Step ι X | present ξ i} := by
  rw [show {ξ : Step ι X | present ξ i} =
      (fun ξ : Step ι X => ξ i) ⁻¹' ({none}ᶜ) by
        ext ξ
        simp [present_iff_ne_none]]
  exact (measurable_pi_apply i) measurableSet_option_none.compl

/-- The set of slots that are present. -/
def support {ι X : Type*} (ξ : Step ι X) : Set ι :=
  {i | present ξ i}

theorem support_finite_of_fintype
    {ι X : Type*} [Fintype ι] (ξ : Step ι X) :
    (support ξ).Finite := Set.toFinite _

end BranchingWalk

end MeasureTheory

module

public import MeasureTheory.MeasurableSpace.Option

/-!
# Option-valued child-slot encoding

This is the semantic slot encoding: `some x` is a child at displacement `x`
and `none` is an absent slot.  Absence is a first-class value, so a slot field
may have no children at all.

The file carries the primitive type, its measurable structure, the presence
predicate, the support of a step, and the zero-defaulted slot reading.  A slot is read
directly as `ξ i`; the zero-defaulted reading `value' ξ i` is separate because
it needs a `Zero X` instance and is not part of the type of a step.  The
    relation layer is in `Step/Relation.lean`; presence closure and optional
relabeling are in `Step/SiblingClosed.lean` and `Step/SiblingClosable.lean`.
The ordered layer is in `Step/Monotone.lean`, and the slot vocabulary in
`Step/Measurability.lean`. Path displacements are in
`Basic/Displace.lean` and `Basic/DisplacementMap.lean`; realized and marked
tree conversions are in `BranchingWalk/MarkedTree/`.
-/

@[expose] public section

open MeasureTheory
open Classical

namespace Combinatorics

namespace Branching

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

def survive {ι X : Type*}
    (ξ : Step ι X) (i : ι) : Prop := ∃ x, ξ i = some x

theorem survive_iff_ne_none {ι X : Type*}
    (ξ : Step ι X) (i : ι) :
    survive ξ i ↔ ξ i ≠ none := by
  cases h : ξ i with
  | none => simp [survive, h]
  | some x => simp [survive, h]

theorem survive_measurableSet
    {ι X : Type*} [MeasurableSpace X] (i : ι) :
    MeasurableSet {ξ : Step ι X | survive ξ i} := by
  rw [show {ξ : Step ι X | survive ξ i} =
      (fun ξ : Step ι X => ξ i) ⁻¹' ({none}ᶜ) by
        ext ξ
        simp [survive_iff_ne_none]]
  exact (measurable_pi_apply i) measurableSet_option_none.compl

/-- The set of slots that are survive. -/
def support {ι X : Type*} (ξ : Step ι X) : Set ι :=
  {i | survive ξ i}

/-- A step is finitely supported when only finitely many of its slots carry a child. This is an
assumption about the step and not about the slot type: it is what lets the children be listed from the
left and relabeled onto an initial segment with increasing marks. -/
class Step.IsFinitelySupported {ι X : Type*} (ξ : Step ι X) : Prop where
  finite : (support ξ).Finite

theorem support_finite_of_fintype
    {ι X : Type*} [Fintype ι] (ξ : Step ι X) :
    (support ξ).Finite := Set.toFinite _

end Branching

end Combinatorics

end

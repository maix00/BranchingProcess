/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Slot
import MeasureTheory.BranchingWalk.Step.Selection.FirstN
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of first and second selected child slots

## Public declarations

For a measurable finite selection \(R(\xi)\), the least selected slot and
the least selected slot after removing the first are measurable random
variables:

\[
\operatorname{Measurable}(\xi\mapsto\operatorname{firstSelectedSlot}(R)(\xi)),
\qquad
\operatorname{Measurable}(\xi\mapsto\operatorname{secondSelectedSlot}(R)(\xi)).
\]

- `Combinatorics.Branching.Step.FiniteSelection.firstSelectedSlot_measurable`
  states that a measurable finite step selection has a measurable least
  selected slot.
- `Combinatorics.Branching.Step.FiniteSelection.secondSelectedSlot_measurable`
  states the same for the least selected slot after removing the first.
- `Combinatorics.Branching.Step.FiniteSelection.firstTwoBySlotOrder_measurable`
  states that selecting the first two slots of a branching step is measurable.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching.Step.FiniteSelection

variable {α X : Type*}

open _root_.Combinatorics.Selection.NSelection

theorem firstSelectedSlot_measurable [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [LinearOrder α]
    [OrderBot α] [MeasurableSpace X]
    (R : _root_.Combinatorics.Branching.Step.FiniteSelection α X)
    (hR : Measurable R.select) : Measurable (firstSelectedSlot R) := by
  let f : Finset α → α := fun s => if h : s.Nonempty then s.min' h else ⊥
  have hf : Measurable f := measurable_of_countable f
  have heq : firstSelectedSlot R = f ∘ R.select := by
    funext ξ
    rfl
  rw [heq]
  exact hf.comp hR

theorem secondSelectedSlot_measurable [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : _root_.Combinatorics.Branching.Step.FiniteSelection α X)
    (hR : Measurable R.select) :
    Measurable (secondSelectedSlot R) := by
  classical
  let f : Finset α → α := fun s =>
    let first := if h : s.Nonempty then s.min' h else ⊥
    if h : s.erase first |>.Nonempty then s.erase first |>.min' h else ⊥
  have hf : Measurable f := measurable_of_countable f
  have heq : secondSelectedSlot R = f ∘ R.select := by
    funext ξ
    rfl
  rw [heq]
  exact hf.comp hR

theorem firstTwoBySlotOrder_measurable [Countable α]
    [MeasurableSpace X] [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] :
    Measurable
      (firstNBySlotOrder (α := α) (X := X) 2).select := by
  let value : Step α X → α → α := fun _ i => i
  let admits : ∀ ξ : Step α X,
      AdmitsFirstNBy 2 (value ξ) (support ξ) := by
    intro ξ
    exact admitsFirstNBySlotOrder 2 ξ
  have hkey : ∀ p q : α, Measurable fun ξ : Step α X =>
      valueKey (value ξ) q < valueKey (value ξ) p := by
    intro p q
    by_cases h : q < p
    · simp [value, valueKey, Prod.Lex.lt_iff, h]
    · simp [value, valueKey, Prod.Lex.lt_iff, h]
  simpa [Combinatorics.Branching.Step.FiniteSelection.firstNBySlotOrder,
    Combinatorics.Branching.Step.FiniteSelection.firstNBy, value, admits] using
    (firstNBy_measurable 2 value admits hkey)

end Combinatorics.Branching.Step.FiniteSelection

end

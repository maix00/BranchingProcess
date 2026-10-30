/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Potential
public import Combinatorics.BranchingWalk.Step.Map
public import Combinatorics.BranchingWalk.Step.Ordering.Monotone

/-!
# Ordering child slots through a real-valued potential

An arbitrary mark space can be ordered through a measurable real-valued
potential. This module connects the mark-level `Potential` interface to the
slot-order condition and its measurable event.

## Public declarations

- `Step.IsOrderedBy φ ξ` means `ξ.map φ ∈ orderedSteps`.
- `orderedBySteps φ = {ξ | ξ.IsOrderedBy φ}`; `mem_orderedBySteps_iff`
  gives this membership equivalence.
- `orderedBySteps_measurable` proves measurability of
  `orderedBySteps φ` when the slot type is countable.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching

/-- A step is ordered by `φ` when its marks, observed through `φ`, form an
increasing step. -/
def Step.IsOrderedBy {ι X : Type*} [LT ι] [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X) : Prop :=
  (ξ.map φ) ∈ orderedSteps

/-- The set of steps ordered by a real-valued potential. -/
def orderedBySteps {ι X : Type*} [LT ι] [MeasurableSpace X]
    (φ : Potential X) : Set (Step ι X) :=
  {ξ | ξ.IsOrderedBy φ}

@[simp] theorem mem_orderedBySteps_iff {ι X : Type*} [LT ι]
    [MeasurableSpace X] (φ : Potential X) (ξ : Step ι X) :
    ξ ∈ orderedBySteps φ ↔ ξ.IsOrderedBy φ := Iff.rfl

theorem orderedBySteps_measurable {ι X : Type*} [Countable ι] [LT ι]
    [MeasurableSpace X] (φ : Potential X) :
    MeasurableSet (orderedBySteps (ι := ι) φ) := by
  change MeasurableSet ((Step.map φ) ⁻¹'
    (orderedSteps : Set (Step ι ℝ)))
  exact (Step.map_measurable φ.measurable_toFun) orderedSteps_measurable

end Combinatorics.Branching

end

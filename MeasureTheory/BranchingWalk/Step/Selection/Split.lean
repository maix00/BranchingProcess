/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Split
public import MeasureTheory.BranchingWalk.Step.Selection.Slot
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of selected splits

## Public declarations

If `R.select` is measurable, then the event of retaining at least two
children is measurable:

\[
\operatorname{splitBy}(R)=\{\xi:2\leq |R(\xi)|\}.
\]

`Combinatorics.Branching.Step.FiniteSelection.splitBy_measurable` proves this
for a countable slot type.
-/

@[expose] public section

open MeasureTheory

namespace Combinatorics.Branching.Step.FiniteSelection

theorem splitBy_measurable {α X : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) : MeasurableSet (splitBy R) := by
  change MeasurableSet {ξ | 2 ≤ (R ξ).card}
  have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hR
  exact hcard measurableSet_Ici

end Combinatorics.Branching.Step.FiniteSelection

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The order on measurable spaces

Measurable spaces are ordered by inclusion of their measurable sets. Thus a
strict comparison `m₁ < m₂` is witnessed by a set measurable for `m₂` and not
measurable for `m₁`.

## Public declarations

- `MeasurableSpace.exists_measurableSet_not_mem_of_lt` states
  `m₁ < m₂ → ∃ s, MeasurableSet[m₂] s ∧ ¬ MeasurableSet[m₁] s`.
-/

@[expose] public section

open scoped MeasureTheory

namespace MeasurableSpace

/-- A strict inclusion of measurable spaces is witnessed by a set measurable
for the larger space and not measurable for the smaller one. -/
theorem exists_measurableSet_not_mem_of_lt {α : Type*}
    {m₁ m₂ : MeasurableSpace α} (h : m₁ < m₂) :
    ∃ s, MeasurableSet[m₂] s ∧ ¬ MeasurableSet[m₁] s := by
  by_contra h'
  push Not at h'
  exact h.ne (le_antisymm h.le h')

end MeasurableSpace

end

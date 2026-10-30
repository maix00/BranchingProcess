/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Interval.Set.Basic

/-!
# Lower-tail comparison of measures

## Public declarations

- `Measure.LowerTailDominates μ ν` means
  `∀ a, μ (Set.Iic a) ≤ ν (Set.Iic a)` on a measurable preorder. It compares
  measures on every principal lower set and requires no finiteness or
  probability normalization.
- `Measure.lowerTailDominates_refl` and
  `Measure.lowerTailDominates_trans` give reflexivity and transitivity.
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [Preorder α]

/-- The first measure has no more mass than the second on any principal lower set. -/
def LowerTailDominates (μ ν : Measure α) : Prop :=
  ∀ a : α, μ (Set.Iic a) ≤ ν (Set.Iic a)

theorem lowerTailDominates_refl (μ : Measure α) :
    LowerTailDominates μ μ :=
  fun _ => le_rfl

theorem lowerTailDominates_trans {μ ν ρ : Measure α}
    (hμν : LowerTailDominates μ ν) (hνρ : LowerTailDominates ν ρ) :
    LowerTailDominates μ ρ :=
  fun a => le_trans (hμν a) (hνρ a)

end MeasureTheory.Measure

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Count

/-!
# Integer-valued measures

A measure is integer-valued when every measurable set has mass in
`ℕ ∪ {∞}`. This property concerns the measure itself and does not assert
that it admits an enumerable Dirac representation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

namespace Measure

variable {X : Type*} [MeasurableSpace X]

/-- A measure whose value on each measurable set is a natural number or
infinity. -/
def IsIntegerValued (μ : Measure X) : Prop :=
  ∀ s : Set X, MeasurableSet s → μ s = ∞ ∨ ∃ n : ℕ, μ s = n

theorem isIntegerValued_zero : IsIntegerValued (0 : Measure X) := by
  intro s hs
  exact Or.inr ⟨0, by simp⟩

/-- The counting measure is integer-valued, by its evaluation as the extended
cardinality of a measurable set. -/
theorem isIntegerValued_count : IsIntegerValued (count : Measure X) := by
  intro s hs
  rcases s.finite_or_infinite with hfin | hinf
  · right
    obtain ⟨n, hn⟩ := hfin.exists_encard_eq_coe
    refine ⟨n, ?_⟩
    rw [count_apply hs]
    exact congrArg (fun k : ENat => (k : ℝ≥0∞)) hn
  · left
    rw [count_apply hs]
    exact congrArg (fun k : ENat => (k : ℝ≥0∞)) hinf.encard_eq

end Measure

end MeasureTheory

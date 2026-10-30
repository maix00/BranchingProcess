/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Tightness of finite families of measures

## Public declarations

* `MeasureTheory.isTightMeasureSet_image_of_finite` states that the image of
  a finite index set under a family of measures is tight when each individual
  measure is tight.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- A finite family of individually tight measures is tight. -/
theorem isTightMeasureSet_image_of_finite
    {ι : Type*} (μ : ι → Measure X) {I : Set ι} (hI : I.Finite)
    (hsingle : ∀ i, IsTightMeasureSet {μ i}) :
    IsTightMeasureSet (μ '' I) := by
  classical
  induction I, hI using Set.Finite.induction_on with
  | empty =>
      rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
      intro ε hε
      refine ⟨∅, isCompact_empty, ?_⟩
      intro ν hν
      simp at hν
  | @insert i I hi hI ih =>
      rw [Set.image_insert_eq]
      have himage : insert (μ i) (μ '' I) = {μ i} ∪ (μ '' I) := by
        ext ν
        simp
      rw [himage]
      exact (hsingle i).union ih

end MeasureTheory

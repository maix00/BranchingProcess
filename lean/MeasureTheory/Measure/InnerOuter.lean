/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Inner measure and measurable-subset bounds

This file defines inner measure as the supremum over measurable subsets and
records the elementary comparison with the measure's outer-measure value.
It is independent of a particular probability or path-space application.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The inner measure of a set, defined as the supremum of the measures of its
measurable subsets. -/
noncomputable def innerMeasure (μ : Measure Ω) (s : Set Ω) : ℝ≥0∞ :=
  ⨆ t : {u : Set Ω // MeasurableSet u ∧ u ⊆ s}, μ t.1

theorem innerMeasure_mono (μ : Measure Ω) {s t : Set Ω} (hst : s ⊆ t) :
    μ.innerMeasure s ≤ μ.innerMeasure t := by
  classical
  unfold innerMeasure
  refine iSup_le fun u => ?_
  exact le_iSup_of_le ⟨u.1, u.2.1, u.2.2.trans hst⟩ le_rfl

theorem le_innerMeasure_of_measurable (μ : Measure Ω) {s : Set Ω}
    (hs : MeasurableSet s) : μ s ≤ μ.innerMeasure s := by
  classical
  unfold innerMeasure
  exact le_iSup_of_le ⟨s, hs, subset_rfl⟩ le_rfl

theorem innerMeasure_le_measure (μ : Measure Ω) (s : Set Ω) :
    μ.innerMeasure s ≤ μ s := by
  classical
  unfold innerMeasure
  refine iSup_le fun t => ?_
  exact measure_mono t.2.2

/-- A null-measurable set has the same measure as a measurable subset, so its
measure is bounded by the inner measure of any superset. -/
theorem measure_le_innerMeasure_of_nullMeasurableSet_subset
    (μ : Measure Ω) {s t : Set Ω} (hs : NullMeasurableSet s μ) (hst : s ⊆ t) :
    μ s ≤ μ.innerMeasure t := by
  obtain ⟨u, hu_s, hu_measurable, hu_ae⟩ := hs.exists_measurable_subset_ae_eq
  calc
    μ s = μ u := (measure_congr hu_ae).symm
    _ ≤ μ.innerMeasure t :=
      (le_innerMeasure_of_measurable μ hu_measurable).trans
        (innerMeasure_mono μ (hu_s.trans hst))

/-- On a null-measurable set, inner measure agrees with measure. -/
theorem innerMeasure_eq_measure_of_nullMeasurableSet
    (μ : Measure Ω) {s : Set Ω} (hs : NullMeasurableSet s μ) :
    μ.innerMeasure s = μ s := by
  apply le_antisymm (innerMeasure_le_measure μ s)
  exact measure_le_innerMeasure_of_nullMeasurableSet_subset μ hs subset_rfl

end MeasureTheory.Measure

end

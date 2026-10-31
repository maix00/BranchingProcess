/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Capacity.Choquet
public import MeasureTheory.MeasurableSpace.CadlagPath.PathClass.StepCorridor.Measurable
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Null-measurability of exact M₂ corridors

The event remains the pointwise-strict corridor from `PathClass.Basic`.  Its
complement is the projection of the Borel path-time violation relation, and
the local axiom-clean Choquet projection theorem makes this projection
null-measurable under every finite path law.

## Public declarations

- Under every finite Borel path law P, the path-time violation projection
  and the exact pointwise-strict M₂ corridor event are P-null-measurable.
  For \(V_c=\{f:\exists t,\,(t,f)\in c.\mathrm{violationAt}\}\), both
  sets satisfy
  \[
  \operatorname{NullMeasurableSet}_{P}(V_c),\qquad
  \operatorname{NullMeasurableSet}_{P}(c.\mathrm{toSet}).
  \]
-/

open Skorokhod.PathClass.StepCorridor

@[expose] public section

open MeasureTheory

namespace Skorokhod.PathClass.StepCorridor

/-- The exact path-time violation projection is null-measurable under every
finite Borel law on càdlàg paths. -/
theorem ContinuousAdmissibleStepCorridor.nullMeasurableSet_violationSet
    (c : ContinuousAdmissibleStepCorridor) (P : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure P] : NullMeasurableSet c.violationSet P := by
  have hproj : c.violationSet = Prod.snd '' c.violationAt := by
    ext path
    simp only [ContinuousAdmissibleStepCorridor.violationSet, Set.mem_ofPred_eq, Set.mem_image, Prod.exists,
      exists_eq_right]
  rw [hproj]
  exact MeasureTheory.Analytic.Paving.MeasurableSet.nullMeasurableSet_snd
    c.measurableSet_violationAt P

/-- The exact pointwise-strict `M₂` corridor is null-measurable under every
finite Borel law on càdlàg paths. -/
theorem ContinuousAdmissibleStepCorridor.nullMeasurableSet_toSet
    (c : ContinuousAdmissibleStepCorridor) (P : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure P] : NullMeasurableSet c.toSet P := by
  have hbadStart : MeasurableSet
      {path : CadlagPath unitInterval ℝ | path ⊥ ≠ 0} := by
    have hstart : Measurable (fun path : CadlagPath unitInterval ℝ => path ⊥) :=
      Skorokhod.measurable_apply ⊥
    rw [show {path : CadlagPath unitInterval ℝ | path ⊥ ≠ 0} =
      {path | path ⊥ = 0}ᶜ by ext path; simp]
    exact (measurableSet_singleton (0 : ℝ)).preimage hstart |>.compl
  have hcompl : NullMeasurableSet c.toSetᶜ P := by
    rw [c.compl_toSet_eq_violationSet]
    exact hbadStart.nullMeasurableSet.union (c.nullMeasurableSet_violationSet P)
  exact hcompl.of_compl

end Skorokhod.PathClass.StepCorridor

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.MeasureTheory.Analytic.Capacity
public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Measurable

/-!
# Null-measurability of exact M₂ corridors

The event remains the pointwise-strict corridor from `PathClass.Basic`.  Its
complement is the projection of the Borel path-time violation relation, and
the local axiom-clean Choquet projection theorem makes this projection
null-measurable under every finite path law.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- The exact path-time violation projection is null-measurable under every
finite Borel law on càdlàg paths. -/
theorem M2Corridor.nullMeasurableSet_violationSet
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure P] : NullMeasurableSet c.violationSet P := by
  have hproj : c.violationSet = Prod.snd '' c.violationAt := by
    ext path
    simp only [M2Corridor.violationSet, Set.mem_ofPred_eq, Set.mem_image, Prod.exists,
      exists_eq_right]
  rw [hproj]
  exact ProbabilityTheory.MeasureTheory.Analytic.Paving.MeasurableSet.nullMeasurableSet_snd
    c.measurableSet_violationAt P

/-- The exact pointwise-strict `M₂` corridor is null-measurable under every
finite Borel law on càdlàg paths. -/
theorem M2Corridor.nullMeasurableSet_toSet
    (c : M2Corridor) (P : Measure (CadlagPath unitInterval ℝ))
    [IsFiniteMeasure P] : NullMeasurableSet c.toSet P := by
  exact c.nullMeasurableSet_toSet_of_violationSet P
    (c.nullMeasurableSet_violationSet P)

end ProbabilityTheory.Process.SmallDeviation.Mogulskii

end

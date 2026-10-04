/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Centered real laws and second moments

These predicates and transport lemmas are distributional facts.  They are
shared by the Donsker, maximal-inequality, entrance, and small-deviation
developments; no random-walk or Mogulskii construction is needed here.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- A real law has mean zero and the specified second moment. -/
def IsCenteredSecondMoment (ν : Measure ℝ) (variance : ℝ) : Prop :=
  (∫ x, x ∂ν) = 0 ∧ (∫ x, x ^ 2 ∂ν) = variance

/-- A real law has mean zero and second moment one. -/
def IsCenteredUnitSecondMoment (ν : Measure ℝ) : Prop :=
  IsCenteredSecondMoment ν 1

/-- A probability law with second moment one has a square-integrable identity
random variable. -/
theorem IsCenteredUnitSecondMoment.memLp_two
    {ν : Measure ℝ} (hν : IsCenteredUnitSecondMoment ν) :
    MemLp id 2 ν := by
  apply (memLp_two_iff_integrable_sq
    stronglyMeasurable_id.aestronglyMeasurable).2
  exact Integrable.of_integral_ne_zero (by
    rw [show (∫ x, id x ^ 2 ∂ν) = 1 by simpa [id] using hν.2]
    norm_num)

/-- Dividing centered increments with second moment `sigma²` by a positive
standard deviation `sigma` produces centered unit-second-moment increments. -/
theorem IsCenteredSecondMoment.map_div
    {ν : Measure ℝ} {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) :
    IsCenteredUnitSecondMoment (ν.map fun x => x / sigma) := by
  constructor
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => x / sigma)
      (f := fun x => x) (measurable_id.div_const sigma).aemeasurable
      measurable_id.aestronglyMeasurable]
    rw [integral_div, hν.1, zero_div]
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => x / sigma)
      (f := fun x => x ^ 2) (measurable_id.div_const sigma).aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simp_rw [div_pow]
    rw [integral_div, hν.2]
    exact div_self (pow_ne_zero 2 hsigma.ne')

/-- Reflection preserves a centered second-moment hypothesis. -/
theorem IsCenteredSecondMoment.map_neg
    {ν : Measure ℝ} {variance : ℝ}
    (hν : IsCenteredSecondMoment ν variance) :
    IsCenteredSecondMoment (ν.map fun x => -x) variance := by
  constructor
  · calc
      (∫ x, x ∂ν.map fun x => -x) = ∫ x, -x ∂ν := by
        simpa using integral_map (μ := ν) (φ := fun x : ℝ => -x)
          measurable_neg.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := by rw [integral_neg, hν.1, neg_zero]
  · rw [integral_map (μ := ν) (φ := fun x : ℝ => -x)
      (f := fun x : ℝ => x ^ 2)
      measurable_neg.aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable]
    simpa using hν.2

/-- Reflection preserves a centered unit-second-moment hypothesis. -/
theorem IsCenteredUnitSecondMoment.map_neg
    {ν : Measure ℝ} (hν : IsCenteredUnitSecondMoment ν) :
    IsCenteredUnitSecondMoment (ν.map fun x => -x) :=
  IsCenteredSecondMoment.map_neg hν

end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF

/-!
# Gaussian interval positivity

The nondegenerate real Gaussian law gives positive mass to every nonempty open
interval.  This is a distribution-level fact and is independent of any random
walk or small-deviation construction.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

/-- A real Gaussian law with nonzero variance assigns positive mass to every
nonempty open interval. -/
theorem gaussianReal_Ioo_pos {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {a b : ℝ} (hab : a < b) :
    0 < gaussianReal μ v (Ioo a b) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hac := gaussianReal_absolutelyContinuous' μ hv
  have hvolume : (volume : Measure ℝ) (Ioo a b) = 0 := hac hzero
  have hpositive : 0 < (volume : Measure ℝ) (Ioo a b) :=
    (Measure.measure_Ioo_pos (volume : Measure ℝ)).2 hab
  exact hpositive.ne' hvolume

/-- The centered nondegenerate real Gaussian law has CDF strictly between
zero and one at zero. The proof uses positive mass on open intervals on both
sides of zero, so it does not depend on a density formula for the CDF. -/
theorem cdf_gaussianReal_zero_lt_one {v : ℝ≥0} (hv : v ≠ 0) :
    0 < cdf (gaussianReal 0 v) 0 ∧ cdf (gaussianReal 0 v) 0 < 1 := by
  let μ : Measure ℝ := gaussianReal 0 v
  have hμ : IsProbabilityMeasure μ := by infer_instance
  have hμfinite : IsFiniteMeasure μ := by infer_instance
  have hneg : 0 < μ.real (Ioo (-1 : ℝ) 0) := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos
    · exact (gaussianReal_Ioo_pos hv (by norm_num)).ne'
    · exact measure_ne_top μ _
  have hpos : 0 < μ.real (Ioo (0 : ℝ) 1) := by
    rw [measureReal_def]
    apply ENNReal.toReal_pos
    · exact (gaussianReal_Ioo_pos hv (by norm_num)).ne'
    · exact measure_ne_top μ _
  have hneg_le : μ.real (Ioo (-1 : ℝ) 0) ≤ μ.real (Iic 0) :=
    measureReal_mono (by intro x hx; exact hx.2.le)
  have hpos_le : μ.real (Ioo (0 : ℝ) 1) ≤ μ.real (Ioi 0) :=
    measureReal_mono (by intro x hx; exact hx.1)
  have hsum : μ.real (Iic (0 : ℝ)) + μ.real (Ioi 0) = 1 := by
    have hu : Iic (0 : ℝ) ∪ Ioi 0 = Set.univ := by ext x; simp
    have hd : Disjoint (Iic (0 : ℝ)) (Ioi 0) :=
      disjoint_left.mpr (by
        intro x hx₁ hx₂
        simp only [mem_Iic] at hx₁
        exact (not_lt_of_ge hx₁) hx₂)
    have h := measureReal_union hd measurableSet_Ioi
      (measure_ne_top μ _) (measure_ne_top μ _)
    rw [hu, measureReal_def] at h
    simpa [measureReal_def] using h.symm
  have hleft : 0 < μ.real (Iic (0 : ℝ)) := hneg.trans_le hneg_le
  have hright : 0 < μ.real (Ioi (0 : ℝ)) := hpos.trans_le hpos_le
  constructor
  · rw [cdf_eq_real]
    exact hleft
  · rw [cdf_eq_real]
    linarith

end ProbabilityTheory

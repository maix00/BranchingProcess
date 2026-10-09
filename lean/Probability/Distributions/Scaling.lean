/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.CDF

/-!
# Scaling real-valued distributions

This module collects real distribution facts that depend only on pushforwards
under scalar multiplication, independently of any particular family of laws.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Multiplication by a positive scalar preserves the mass of the
nonpositive half-line, and hence the distribution function at zero. -/
theorem cdf_map_mul_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) :
    cdf (μ.map fun x => r * x) 0 = cdf μ 0 := by
  have hmap : (μ.map fun x => r * x) (Set.Iic 0) = μ (Set.Iic 0) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hx
      calc
        x = (r * x) / r := by field_simp [hr.ne']
        _ ≤ 0 / r := div_le_div_of_nonneg_right hx hr.le
        _ = 0 := by simp
    · intro hx
      exact (mul_le_mul_of_nonneg_left hx hr.le).trans_eq (by simp)
  have hreal : (μ.map (fun x => r * x)).real (Set.Iic 0) =
      μ.real (Set.Iic 0) := by
    rw [measureReal_def, measureReal_def, hmap]
  rw [cdf_eq_real, cdf_eq_real]
  exact hreal

end ProbabilityTheory

end

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

## Public declarations

- `ProbabilityTheory.cdf_map_mul`: for a probability measure $\mu$ on
  $\mathbb R$ and $r>0$, $\operatorname{cdf}((y\mapsto ry)_*\mu)(x)=\operatorname{cdf}(\mu)(x/r)$ for every $x\in\mathbb R$.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- A positive scalar dilation transforms the distribution function by the
inverse change of threshold. -/
theorem cdf_map_mul {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {r x : ℝ} (hr : 0 < r) :
    cdf (μ.map fun y => r * y) x = cdf μ (x / r) := by
  have hmap : (μ.map fun y => r * y) (Set.Iic x) = μ (Set.Iic (x / r)) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor
    · intro hx
      calc
        y = (r * y) / r := by field_simp [hr.ne']
        _ ≤ x / r := div_le_div_of_nonneg_right hx hr.le
    · intro hx
      calc
        r * y ≤ r * (x / r) := mul_le_mul_of_nonneg_left hx hr.le
        _ = x := by field_simp [hr.ne']
  have hreal : (μ.map (fun y => r * y)).real (Set.Iic x) =
      μ.real (Set.Iic (x / r)) := by
    rw [measureReal_def, measureReal_def, hmap]
  rw [cdf_eq_real, cdf_eq_real]
  exact hreal

end ProbabilityTheory

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Signs of centered real Gaussian variables

The public theorems in this file are:

- `ProbabilityTheory.gaussianReal_Ioi_zero_pos`:
  a standard Gaussian law gives positive mass to $(0,\infty)$.
- `ProbabilityTheory.gaussianReal_Ioi_zero_eq_standard`:
  for $v>0$, a centered Gaussian law with variance $v$ gives
  $(0,\infty)$ the same mass as the standard Gaussian law.
- `ProbabilityTheory.gaussianReal_Iic_zero_eq_standard`:
  for $v>0$, a centered Gaussian law with variance $v$ gives
  $(-\infty,0]$ the same mass as the standard Gaussian law.

These facts use the positive Gaussian density and its scaling identity
from mathlib's real Gaussian distribution theory. They supply the
uniform increment-sign estimate in the Brownian argument of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Lemma 2.2, p. 481,
Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A standard centered Gaussian law assigns positive mass to the
positive open half-line. -/
theorem gaussianReal_Ioi_zero_pos :
    0 < gaussianReal 0 (1 : ℝ≥0) (Ioi 0) := by
  have hvolume : (volume : Measure ℝ) ≪
      gaussianReal 0 (1 : ℝ≥0) :=
    gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hOpenPos : Measure.IsOpenPosMeasure (gaussianReal 0 (1 : ℝ≥0)) :=
    hvolume.isOpenPosMeasure
  exact (hOpenPos.open_pos _ isOpen_Ioi ⟨1, by norm_num⟩).bot_lt

/-- Multiplying a standard Gaussian by $\sqrt v>0$ preserves its sign
and produces a centered Gaussian with variance $v$. -/
theorem gaussianReal_Ioi_zero_eq_standard
    {v : ℝ≥0} (hv : 0 < v) :
    gaussianReal 0 v (Ioi 0) =
      gaussianReal 0 (1 : ℝ≥0) (Ioi 0) := by
  let c : ℝ := Real.sqrt v
  have hc : 0 < c := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hvar : NNReal.mk (c ^ 2) (sq_nonneg c) = v := by
    apply NNReal.coe_injective
    change c ^ 2 = (v : ℝ)
    exact Real.sq_sqrt v.property
  have hmap : (gaussianReal 0 (1 : ℝ≥0)).map (c * ·) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    simpa only [mul_one] using congrArg (gaussianReal 0) hvar
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  have hpre : (c * ·) ⁻¹' Ioi (0 : ℝ) = Ioi 0 := by
    ext x
    change 0 < c * x ↔ 0 < x
    exact (mul_pos_iff_of_pos_left hc)
  rw [hpre]

/-- Scaling a standard Gaussian by a positive constant preserves the
nonpositive half-line. -/
theorem gaussianReal_Iic_zero_eq_standard
    {v : ℝ≥0} (hv : 0 < v) :
    gaussianReal 0 v (Iic 0) =
      gaussianReal 0 (1 : ℝ≥0) (Iic 0) := by
  let c : ℝ := Real.sqrt v
  have hc : 0 < c := Real.sqrt_pos.2 (by exact_mod_cast hv)
  have hvar : NNReal.mk (c ^ 2) (sq_nonneg c) = v := by
    apply NNReal.coe_injective
    change c ^ 2 = (v : ℝ)
    exact Real.sq_sqrt v.property
  have hmap : (gaussianReal 0 (1 : ℝ≥0)).map (c * ·) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero]
    simpa only [mul_one] using congrArg (gaussianReal 0) hvar
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (c * ·) ⁻¹' Iic (0 : ℝ) = Iic 0 := by
    ext x
    change c * x ≤ 0 ↔ x ≤ 0
    constructor
    · intro hx
      by_contra hx'
      exact (not_le_of_gt (mul_pos hc (lt_of_not_ge hx'))) hx
    · exact mul_nonpos_of_nonneg_of_nonpos hc.le
  rw [hpre]

end ProbabilityTheory

end

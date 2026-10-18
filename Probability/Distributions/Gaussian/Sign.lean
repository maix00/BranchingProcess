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
- `ProbabilityTheory.gaussianReal_Iio_zero_two_mul`:
  for $v>0$, twice the mass of $(-\infty,0)$ is $1$.

These facts use the positive Gaussian density and its scaling identity
from mathlib's real Gaussian distribution theory. They supply the
uniform increment-sign estimate in the Brownian argument of Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.2, p. 481,
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

/-- A nondegenerate centered Gaussian has half of its mass below zero.
The equation is written without division in `ℝ≥0∞`. -/
theorem gaussianReal_Iio_zero_two_mul {v : ℝ≥0} (hv : 0 < v) :
    2 * gaussianReal 0 v (Iio 0) = 1 := by
  let μ : Measure ℝ := gaussianReal 0 v
  have hsym : μ (Iio 0) = μ (Ioi 0) := by
    have hmap : μ.map (fun x : ℝ => -x) = μ := by
      simpa [μ] using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := v))
    calc
      μ (Iio 0) = (μ.map (fun x : ℝ => -x)) (Iio 0) := by rw [hmap]
      _ = μ (Ioi 0) := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
        congr 1
        ext x
        simp
  have hnull : μ ({0} : Set ℝ) = 0 := by
    have hclass : NullSingletonClass μ := nullSingletonClass_gaussianReal hv.ne'
    exact @measure_singleton ℝ _ μ hclass 0
  have hpartition : μ (Iio 0) + μ (Ioi 0) = 1 := by
    have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
      exact Set.disjoint_left.mpr (by intro x hx hy; exact (lt_asymm hx) hy)
    have hunion : (Iio (0 : ℝ)) ∪ Ioi 0 = {0}ᶜ := by
      ext x
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro (h | h)
        · exact ne_of_lt h
        · exact ne_of_gt h
      · exact lt_or_gt_of_ne
    calc
      μ (Iio 0) + μ (Ioi 0) = μ (Iio 0 ∪ Ioi 0) :=
        (measure_union hdisj measurableSet_Ioi).symm
      _ = μ {0}ᶜ := by rw [hunion]
      _ = 1 := by rw [measure_compl (measurableSet_singleton 0) (by finiteness),
        hnull, measure_univ]; simp
  rw [← hsym] at hpartition
  simpa [μ, two_mul] using hpartition

end ProbabilityTheory

end

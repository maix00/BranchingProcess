/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

/-!
# Quantitative bounds for the sinc function

This file records analytic estimates for `Real.sinc` used to compare its defect
`1 - Real.sinc x` with the standard truncation weight `min 1 (x ^ 2)`.

## Main results

* `Real.intervalIntegral_exp_I_symm`:
  `½ ∫_{-1}^1 exp(iux) du = sinc x`.
* `Real.one_sub_sinc_pos`: `0 < 1 - sinc x` when `x ≠ 0`.
* `Real.one_sub_sinc_le_mul_min` and `Real.mul_min_le_one_sub_sinc`:
  `(2/(3π²)) min(1,x²) ≤ 1 - sinc x ≤ 2 min(1,x²)`.
-/

open Complex MeasureTheory
open scoped Real

namespace Real

/-- The symmetric exponential average `½ ∫_{-1}^{1} e^{iux} du` equals `Real.sinc x`
(which is `sin x / x` for `x ≠ 0` and `1` at `x = 0`). -/
theorem intervalIntegral_exp_I_symm (x : ℝ) :
    (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑x * I) = (sinc x : ℂ) := by
  by_cases hx : x = 0
  · subst hx
    have hconst : (fun u : ℝ => Complex.exp (↑u * ↑(0 : ℝ) * I)) = fun _ => (1 : ℂ) := by
      funext u; simp
    have hint : (∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑(0 : ℝ) * I)) = 2 := by
      rw [hconst, intervalIntegral.integral_const]
      show ((1 : ℝ) - (-1 : ℝ)) • (1 : ℂ) = 2
      rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
      push_cast
      norm_num
    rw [hint, sinc_zero, Complex.ofReal_one]
    norm_num
  · have hxC : (↑x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hc : (↑x * I : ℂ) ≠ 0 := mul_ne_zero hxC Complex.I_ne_zero
    have hrw : (∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑x * I))
        = ∫ u in (-1 : ℝ)..1, Complex.exp ((↑x * I) * ↑u) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      congr 1
      ring
    rw [hrw, integral_exp_mul_complex hc, sinc_of_ne_zero hx, Complex.ofReal_div,
        Complex.ofReal_sin]
    have key : Complex.exp (↑x * I * ↑(1 : ℝ)) - Complex.exp (↑x * I * ↑(-1 : ℝ))
        = 2 * (Complex.sin ↑x * I) := by
      rw [Complex.ofReal_one, Complex.ofReal_neg, Complex.ofReal_one, mul_one, mul_neg_one,
          show -(↑x * I) = ((-↑x : ℂ)) * I from by ring, Complex.exp_mul_I, Complex.exp_mul_I,
          Complex.cos_neg, Complex.sin_neg]
      ring
    rw [key]
    field_simp

/-- `1 - Real.sinc x` is strictly positive for `x ≠ 0`. -/
theorem one_sub_sinc_pos {x : ℝ} (hx : x ≠ 0) : 0 < 1 - sinc x := by
  rw [sinc_of_ne_zero hx,
      show (1 : ℝ) - Real.sin x / x = (x - Real.sin x) / x from by field_simp, div_pos_iff]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · right
    refine ⟨?_, hneg⟩
    have h := Real.sin_lt (neg_pos.mpr hneg)
    rw [Real.sin_neg] at h
    linarith
  · exact Or.inl ⟨by linarith [Real.sin_lt hpos], hpos⟩

/-- Quantitative upper bound on `sin` over `[0, π]`:
`sin x ≤ x - (2/(3π²)) x³`, obtained by integrating a cosine bound. -/
private lemma sin_le_sub_cube {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) :
    Real.sin x ≤ x - 2 / (3 * π ^ 2) * x ^ 3 := by
  have hcos : (∫ t in (0 : ℝ)..x, Real.cos t) = Real.sin x := by
    rw [integral_cos]; simp
  have hint_g : IntervalIntegrable (fun t : ℝ => 1 - 2 / π ^ 2 * t ^ 2) volume 0 x :=
    (by fun_prop : Continuous fun t : ℝ => 1 - 2 / π ^ 2 * t ^ 2).intervalIntegrable 0 x
  have hmono : (∫ t in (0 : ℝ)..x, Real.cos t)
      ≤ ∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx0
      (Real.continuous_cos.intervalIntegrable 0 x) hint_g (fun t ht => ?_)
    have htabs : |t| ≤ π := by rw [abs_of_nonneg ht.1]; exact ht.2.trans hxπ
    exact Real.cos_le_one_sub_mul_cos_sq htabs
  have hval : (∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2))
      = x - 2 / (3 * π ^ 2) * x ^ 3 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => 2 / π ^ 2 * t ^ 2).intervalIntegrable 0 x),
        intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, sub_zero]
    ring
  calc Real.sin x = ∫ t in (0 : ℝ)..x, Real.cos t := hcos.symm
    _ ≤ ∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2) := hmono
    _ = x - 2 / (3 * π ^ 2) * x ^ 3 := hval

/-- Numeric inequality supporting the lower bound for `|x| ≥ π`:
`2/(3π²) ≤ 1 - 1/π`. -/
private lemma sinc_lower_const : 2 / (3 * π ^ 2) ≤ 1 - π⁻¹ := by
  have hπ := Real.pi_gt_three
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * π ^ 2)]
  have hprod : (1 - π⁻¹) * (3 * π ^ 2) = 3 * π ^ 2 - 3 * π := by
    field_simp
  rw [hprod]
  nlinarith [hπ, Real.pi_pos]

/-- For every real `x`, `1 - Real.sinc x ≤ 2 min(1, x²)`. -/
theorem one_sub_sinc_le_mul_min (x : ℝ) :
    1 - sinc x ≤ 2 * min 1 (x ^ 2) := by
  have hsinc : sinc x = sinc |x| := by
    rcases abs_choice x with h | h <;> simp [h, Real.sinc_neg]
  rw [hsinc, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  rcases le_or_gt (y ^ 2) 1 with hy1 | hy1
  · rw [min_eq_right hy1]
    by_cases hy00 : y = 0
    · rw [hy00]; simp
    · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy00)
      have hyle1 : y ≤ 1 := by nlinarith [hy1, hy0]
      rw [sinc_of_ne_zero hypos.ne']
      have hsin := Real.sin_ge_sub_cube hy0
      have hydiff : y - Real.sin y ≤ 2 / 9 * y ^ 3 := by
        nlinarith [hsin, mul_nonneg (sq_nonneg y) hy0]
      have hkey : 1 - Real.sin y / y ≤ 2 / 9 * y ^ 2 := by
        rw [show (1 : ℝ) - Real.sin y / y = (y - Real.sin y) / y from by field_simp,
            div_le_iff₀ hypos]
        nlinarith [hydiff]
      nlinarith [hkey, sq_nonneg y]
  · rw [min_eq_left hy1.le]
    have := Real.neg_one_le_sinc y
    linarith

/-- For every real `x`, `(2/(3π²)) min(1, x²) ≤ 1 - Real.sinc x`. -/
theorem mul_min_le_one_sub_sinc (x : ℝ) :
    2 / (3 * π ^ 2) * min 1 (x ^ 2) ≤ 1 - sinc x := by
  have hsinc : sinc x = sinc |x| := by
    rcases abs_choice x with h | h <;> simp [h, Real.sinc_neg]
  rw [hsinc, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  by_cases hy00 : y = 0
  · rw [hy00]; simp
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy00)
    have hcpos : (0 : ℝ) ≤ 2 / (3 * π ^ 2) := by positivity
    rcases le_or_gt y π with hyπ | hyπ
    · have hsin := sin_le_sub_cube hy0 hyπ
      have hkey : 2 / (3 * π ^ 2) * y ^ 2 ≤ 1 - sinc y := by
        rw [sinc_of_ne_zero hypos.ne',
            show (1 : ℝ) - Real.sin y / y = (y - Real.sin y) / y from by field_simp,
            le_div_iff₀ hypos]
        nlinarith [hsin]
      calc 2 / (3 * π ^ 2) * min 1 (y ^ 2)
          ≤ 2 / (3 * π ^ 2) * y ^ 2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hcpos
        _ ≤ 1 - sinc y := hkey
    · have hy2 : 1 ≤ y ^ 2 := by nlinarith [Real.pi_gt_three, hyπ]
      rw [min_eq_left hy2, mul_one]
      have hsinc_le : sinc y ≤ y⁻¹ := by
        have := Real.sinc_le_inv_abs hypos.ne'
        rwa [abs_of_pos hypos] at this
      have hinv : y⁻¹ ≤ π⁻¹ := inv_anti₀ Real.pi_pos hyπ.le
      calc 2 / (3 * π ^ 2) ≤ 1 - π⁻¹ := sinc_lower_const
        _ ≤ 1 - y⁻¹ := by linarith
        _ ≤ 1 - sinc y := by linarith

end Real

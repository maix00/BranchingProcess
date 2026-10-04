/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounds for the inverse cosine Tauberian kernel

The kernel is defined by a sinc integral. This module proves its
continuity, bounds, decay, and Mellin integrability.
-/

open MeasureTheory Set
open Filter Asymptotics
open scoped Interval RealInnerProductSpace Complex Topology

@[expose] public section

namespace Analysis.Fourier.CosineTauberian

noncomputable def cosineTauberianKernel (t : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2 * Real.sinc (t * r)

/-- The sinc representation makes the Tauberian kernel continuous at every
frequency, including zero. -/
theorem continuous_cosineTauberianKernel :
    Continuous cosineTauberianKernel := by
  change Continuous fun t : ℝ =>
    ∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2 * Real.sinc (t * r)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) 0 1

private theorem intervalIntegrable_cosineTauberianKernel_integrand (t : ℝ) :
    IntervalIntegrable (fun r : ℝ => (1 - r) * r ^ 2 * Real.sinc (t * r))
      volume 0 1 := by
  exact (by fun_prop : Continuous fun r : ℝ => (1 - r) * r ^ 2 * Real.sinc (t * r))
    |>.intervalIntegrable 0 1

/-- The sinc representation is bounded uniformly, including at the origin. -/
theorem abs_cosineTauberianKernel_le (t : ℝ) :
    |cosineTauberianKernel t| ≤ 1 / 12 := by
  rw [cosineTauberianKernel, ← Real.norm_eq_abs]
  let f : ℝ → ℝ := fun r => (1 - r) * r ^ 2 * Real.sinc (t * r)
  have hf : IntervalIntegrable f volume 0 1 := by
    exact (by fun_prop : Continuous f).intervalIntegrable 0 1
  have hab : (0 : ℝ) ≤ 1 := by norm_num
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) (f := f) hab
  have hnormInt : IntervalIntegrable (fun r : ℝ => ‖f r‖) volume 0 1 := by
    exact (by fun_prop : Continuous fun r : ℝ => ‖f r‖).intervalIntegrable 0 1
  have hweightInt : IntervalIntegrable (fun r : ℝ => (1 - r) * r ^ 2)
      volume 0 1 := by
    exact (by fun_prop : Continuous fun r : ℝ => (1 - r) * r ^ 2)
      |>.intervalIntegrable 0 1
  have hpoint : ∀ r ∈ Set.Icc (0 : ℝ) 1, ‖f r‖ ≤ (1 - r) * r ^ 2 := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hweight : 0 ≤ (1 - r) * r ^ 2 :=
      mul_nonneg (sub_nonneg.mpr hr1) (sq_nonneg r)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight]
    calc
      (1 - r) * r ^ 2 * |Real.sinc (t * r)| ≤
          (1 - r) * r ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sinc_le_one _) hweight
      _ = (1 - r) * r ^ 2 := by ring
  have hmono := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (μ := volume) (f := fun r => ‖f r‖) (g := fun r => (1 - r) * r ^ 2)
    hab hnormInt hweightInt hpoint
  have hweight : (∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2) = 1 / 12 := by
    rw [show (fun r : ℝ => (1 - r) * r ^ 2) = fun r => r ^ 2 - r ^ 3 from by
      funext r
      ring]
    rw [intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_pow (μ := volume) (a := 0) (b := 1) 2)
      (intervalIntegral.intervalIntegrable_pow (μ := volume) (a := 0) (b := 1) 3),
      integral_pow, integral_pow]
    norm_num
  calc
    ‖∫ r in (0 : ℝ)..1, f r‖ ≤ ∫ r in (0 : ℝ)..1, ‖f r‖ := hnorm
    _ ≤ ∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2 := hmono
    _ = 1 / 12 := hweight

/-- The scaled sine integral in the kernel has an elementary antiderivative. -/
private theorem integral_cosineTauberian_numerator {t : ℝ} (_ht : 0 < t) :
    (∫ q in (0 : ℝ)..t, (t - q) * q * Real.sin q) =
      2 * (1 - Real.cos t) - t * Real.sin t := by
  let G : ℝ → ℝ := fun q =>
    -t * q * Real.cos q + t * Real.sin q + q ^ 2 * Real.cos q -
      2 * q * Real.sin q - 2 * Real.cos q
  have hdiff (q : ℝ) : DifferentiableAt ℝ G q := by
    dsimp [G]
    fun_prop
  have hderivEq (q : ℝ) : HasDerivAt G ((t - q) * q * Real.sin q) q := by
    have hderiv : deriv G q = (t - q) * q * Real.sin q := by
      simp (disch := fun_prop) [G, deriv_fun_add, deriv_fun_sub,
        deriv_fun_mul, deriv_fun_pow, Real.deriv_sin, Real.deriv_cos]
      ring
    exact (hdiff q).hasDerivAt.congr_deriv hderiv
  have hderiv : ∀ q ∈ uIcc (0 : ℝ) t,
      HasDerivAt G ((t - q) * q * Real.sin q) q := by
    intro q _
    exact hderivEq q
  have hint : IntervalIntegrable (fun q : ℝ => (t - q) * q * Real.sin q)
      volume 0 t := by
    exact (by fun_prop : Continuous fun q : ℝ => (t - q) * q * Real.sin q)
      |>.intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [G]
  rw [Real.sin_zero, Real.cos_zero]
  ring

/-- For positive frequencies, the sinc representation is exactly the quotient
kernel used in the twice-integrated cosine-tail identity. -/
theorem cosineTauberianKernel_eq_quotient {t : ℝ} (ht : 0 < t) :
    cosineTauberianKernel t =
      (2 * (1 - Real.cos t) - t * Real.sin t) / t ^ 4 := by
  let g : ℝ → ℝ := fun q => (t - q) * q * Real.sin q
  have hcongr : (∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2 * Real.sinc (t * r)) =
      ∫ r in (0 : ℝ)..1, (t ^ 3)⁻¹ * g (t * r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with r
    intro _hrI
    by_cases hr : r = 0
    · simp [hr, g]
    · rw [Real.sinc_of_ne_zero (mul_ne_zero ht.ne' hr)]
      dsimp [g]
      field_simp
  have hchange := intervalIntegral.integral_comp_mul_right
    (f := g) (a := (0 : ℝ)) (b := 1) (c := t) ht.ne'
  have hchange' : (∫ r in (0 : ℝ)..1, g (t * r)) =
      t⁻¹ * (∫ q in (0 : ℝ)..t, g q) := by
    simpa [smul_eq_mul, mul_comm] using hchange
  change (∫ r in (0 : ℝ)..1, (1 - r) * r ^ 2 * Real.sinc (t * r)) = _
  rw [hcongr, intervalIntegral.integral_const_mul, hchange']
  rw [integral_cosineTauberian_numerator ht]
  field_simp [ne_of_gt ht]

/-- The quotient kernel has cubic decay at infinity. The uniform bound near
zero comes from its sinc representation, while this estimate controls the
Mellin tail. -/
theorem abs_cosineTauberianKernel_le_tail {t : ℝ} (ht : 1 ≤ t) :
    |cosineTauberianKernel t| ≤ 4 / t ^ 4 + 1 / t ^ 3 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [cosineTauberianKernel_eq_quotient htpos]
  have hcos : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  have hsin : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hshift : |1 - Real.cos t| ≤ 2 := by
    have hcos' := abs_le.mp hcos
    rw [abs_le]
    constructor <;> nlinarith
  have hnum :
      |2 * (1 - Real.cos t) - t * Real.sin t| ≤ 4 + t := by
    calc
      |2 * (1 - Real.cos t) - t * Real.sin t| ≤
          |2 * (1 - Real.cos t)| + |t * Real.sin t| := abs_sub _ _
      _ = 2 * |1 - Real.cos t| + t * |Real.sin t| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul,
          abs_of_pos htpos]
      _ ≤ 4 + t := by nlinarith
  have ht4 : 0 < t ^ 4 := pow_pos htpos _
  rw [abs_div, abs_of_pos ht4]
  calc
    |2 * (1 - Real.cos t) - t * Real.sin t| / t ^ 4 ≤
        (4 + t) / t ^ 4 := div_le_div_of_nonneg_right hnum (le_of_lt ht4)
    _ = 4 / t ^ 4 + 1 / t ^ 3 := by
      field_simp [ne_of_gt htpos]

/-- The absolute Mellin integrand for the Tauberian kernel is integrable on the
positive half-line exactly in the range needed here, `0 < α < 2`. -/
theorem integrableOn_rpow_mul_abs_cosineTauberianKernel
    {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    IntegrableOn (fun s : ℝ => s ^ α * |cosineTauberianKernel s|) (Ioi 0) := by
  let f : ℝ → ℝ := fun s => |cosineTauberianKernel s|
  have hf_local : LocallyIntegrableOn f (Ioi 0) := by
    have hfcont : Continuous f := by
      exact continuous_abs.comp continuous_cosineTauberianKernel
    exact hfcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_top : f =O[atTop] (fun s : ℝ => s ^ (-3 : ℝ)) := by
    apply IsBigO.of_bound 5
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hK := abs_cosineTauberianKernel_le_tail hs
    have hs3 : 0 < s ^ 3 := by positivity
    have hs3nonneg : 0 ≤ s ^ 3 := le_of_lt hs3
    have hs4 : s ^ 3 ≤ s ^ 4 := by
      nlinarith [mul_nonneg hs3nonneg (sub_nonneg.mpr hs)]
    have hdiv : 4 / s ^ 4 ≤ 4 / s ^ 3 := by
      apply (div_le_div_iff₀ (by positivity : 0 < s ^ 4) (by positivity : 0 < s ^ 3)).2
      nlinarith
    have hpow : s ^ (-3 : ℝ) = 1 / s ^ 3 := by
      rw [Real.rpow_neg hspos.le]
      simp [one_div]
    calc
      ‖f s‖ = |cosineTauberianKernel s| := by simp [f]
      _ ≤ 4 / s ^ 4 + 1 / s ^ 3 := hK
      _ ≤ 4 / s ^ 3 + 1 / s ^ 3 := add_le_add hdiv le_rfl
      _ = 5 * ‖s ^ (-3 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hspos.le _), hpow]
        ring
  have hf_bot : f =O[𝓝[>] (0 : ℝ)] (fun s : ℝ => s ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound'
    filter_upwards [] with s
    calc
      ‖f s‖ = |cosineTauberianKernel s| := by simp [f]
      _ ≤ 1 := (abs_cosineTauberianKernel_le s).trans (by norm_num)
      _ = ‖s ^ (-(0 : ℝ))‖ := by simp
  have hint := mellin_convergent_of_isBigO_scalar
    (a := 3) (b := 0) (s := α + 1) hf_local hf_top (by linarith)
      hf_bot (by linarith)
  simpa [f, show α + 1 - 1 = α by ring] using hint

/-- The Tauberian kernel itself is integrable on the positive half-line.  This
is the `α = 1` weighted estimate away from zero, together with continuity near
zero. -/
theorem integrableOn_cosineTauberianKernel :
    IntegrableOn cosineTauberianKernel (Ioi 0) := by
  have hsmall : IntegrableOn cosineTauberianKernel (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact continuous_cosineTauberianKernel.intervalIntegrable 0 1
  have hmajor : IntegrableOn
      (fun s : ℝ => 4 * s ^ (-4 : ℝ) + s ^ (-3 : ℝ)) (Ioi 1) := by
    have h4 : IntegrableOn (fun s : ℝ => s ^ (-4 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    have h3 : IntegrableOn (fun s : ℝ => s ^ (-3 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    exact h4.const_mul 4 |>.add h3
  have htail : IntegrableOn cosineTauberianKernel (Ioi 1) := by
    apply hmajor.integrable.mono'
      continuous_cosineTauberianKernel.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := lt_trans zero_lt_one hs
    have hsone : 1 ≤ s := le_of_lt hs
    have hK := abs_cosineTauberianKernel_le_tail hsone
    have hpow4 : s ^ (-4 : ℝ) = 1 / s ^ 4 := by
      rw [Real.rpow_neg hspos.le]
      simp [one_div]
    have hpow3 : s ^ (-3 : ℝ) = 1 / s ^ 3 := by
      rw [Real.rpow_neg hspos.le]
      simp [one_div]
    have hmajorEq :
        4 * s ^ (-4 : ℝ) + s ^ (-3 : ℝ) = 4 / s ^ 4 + 1 / s ^ 3 := by
      rw [hpow4, hpow3]
      ring
    rw [Real.norm_eq_abs, hmajorEq]
    exact hK
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  exact ⟨hsmall, htail⟩


end Analysis.Fourier.CosineTauberian

end

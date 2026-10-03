/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.CharacteristicFunction.Tauberian.Kernel.Basic
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier inversion for the cosine Tauberian kernel

A compactly supported spline has the Tauberian kernel as its cosine transform.
Fourier inversion then gives the kernel identity needed for the twice-integrated tail.
-/

open MeasureTheory Set
open scoped Interval FourierTransform RealInnerProductSpace Complex

@[expose] public section

namespace ProbabilityTheory

/-- The compact cubic profile paired with the cosine Tauberian kernel under
Fourier inversion. -/
noncomputable def cosineTauberianProfile (x : ℝ) : ℝ :=
  (max (1 - |x|) 0) ^ 2 * (1 + 2 * |x|) / 6

theorem continuous_cosineTauberianProfile :
    Continuous cosineTauberianProfile := by
  change Continuous fun x : ℝ => (max (1 - |x|) 0) ^ 2 * (1 + 2 * |x|) / 6
  fun_prop

private theorem cosineTauberianProfile_eq_poly {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    cosineTauberianProfile r = 1 / 6 - r ^ 2 / 2 + r ^ 3 / 3 := by
  simp [cosineTauberianProfile, abs_of_nonneg hr₀,
    max_eq_left (sub_nonneg.mpr hr₁)]
  ring

private theorem cosineTauberianProfile_zero_of_abs_ge {x : ℝ}
    (hx : 1 ≤ |x|) : cosineTauberianProfile x = 0 := by
  simp [cosineTauberianProfile, max_eq_right (sub_nonpos.mpr hx)]

/-- The Fourier profile encodes the capped cubic obtained by integrating a
two-sided tail twice. -/
theorem cosineTauberianProfile_gap_eq_cappedCubic
    {x y : ℝ} (hx : 0 < x) :
    x ^ 3 * (cosineTauberianProfile 0 -
      cosineTauberianProfile (y / x)) =
        x * (min |y| x) ^ 2 / 2 - (min |y| x) ^ 3 / 3 := by
  have hzero : cosineTauberianProfile 0 = 1 / 6 := by
    norm_num [cosineTauberianProfile]
  have hratioAbs : |y / x| = |y| / x := by
    rw [abs_div, abs_of_pos hx]
  by_cases hy : |y| ≤ x
  · have hr₀ : 0 ≤ |y| / x := div_nonneg (abs_nonneg _) hx.le
    have hr₁ : |y| / x ≤ 1 := by
      apply (div_le_iff₀ hx).2
      nlinarith
    have hpoly := cosineTauberianProfile_eq_poly hr₀ hr₁
    have hprofEq : cosineTauberianProfile (y / x) =
        cosineTauberianProfile (|y| / x) := by
      unfold cosineTauberianProfile
      rw [hratioAbs, abs_of_nonneg hr₀]
    have hprofile : cosineTauberianProfile (y / x) =
        1 / 6 - (|y| / x) ^ 2 / 2 + (|y| / x) ^ 3 / 3 := by
      rw [hprofEq]
      exact hpoly
    rw [hzero, hprofile, min_eq_left hy]
    field_simp [ne_of_gt hx]
    ring
  · have hxy : x < |y| := lt_of_not_ge hy
    have hr₁ : 1 ≤ |y| / x := by
      apply (le_div_iff₀ hx).2
      nlinarith
    have hprofile : cosineTauberianProfile (y / x) = 0 := by
      have harg : 1 ≤ |y / x| := by rw [hratioAbs]; exact hr₁
      exact cosineTauberianProfile_zero_of_abs_ge harg
    rw [hzero, hprofile, min_eq_right (le_of_lt hxy)]
    field_simp [ne_of_gt hx]
    ring

/-- The Fourier inversion profile has compact support in `[-1,1]`. -/
private theorem cosineTauberianProfile_hasCompactSupport :
    HasCompactSupport cosineTauberianProfile := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  apply Function.support_subset_iff'.2
  intro x hx
  have hx' : x < -1 ∨ 1 < x := by
    by_contra h'
    have h'' := not_or.mp h'
    exact hx ⟨le_of_not_gt h''.1, le_of_not_gt h''.2⟩
  rcases hx' with hx' | hx'
  · have hax : 1 ≤ |x| := by
      rw [abs_of_neg (by linarith : x < 0)]
      linarith
    exact cosineTauberianProfile_zero_of_abs_ge hax
  · have hax : 1 ≤ |x| := by
      rw [abs_of_pos (by linarith : 0 < x)]
      linarith
    exact cosineTauberianProfile_zero_of_abs_ge hax

private theorem cosineTauberianProfile_integrable :
    Integrable cosineTauberianProfile :=
  continuous_cosineTauberianProfile.integrable_of_hasCompactSupport
    cosineTauberianProfile_hasCompactSupport

/-- On the positive half of its support, the spline's cosine transform is the
Tauberian kernel. -/
private theorem intervalIntegral_cosineTauberianProfile_mul_cos_eq_kernel
    {t : ℝ} (ht : 0 < t) :
    (∫ r in (0 : ℝ)..1,
      cosineTauberianProfile r * Real.cos (t * r)) = cosineTauberianKernel t := by
  let G : ℝ → ℝ := fun r =>
    (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.sin (t * r) / t +
      (-r + r ^ 2) * Real.cos (t * r) / t ^ 2 -
      (-1 + 2 * r) * Real.sin (t * r) / t ^ 3 -
      2 * Real.cos (t * r) / t ^ 4
  have hGdiff (r : ℝ) : DifferentiableAt ℝ G r := by
    dsimp [G]
    fun_prop
  have hGderiv (r : ℝ) :
      HasDerivAt G ((1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r)) r := by
    have hderiv : deriv G r =
        (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r) := by
      simp (disch := fun_prop) [G, deriv_fun_add, deriv_fun_sub, deriv_fun_mul,
        deriv_fun_pow]
      field_simp
      ring
    exact (hGdiff r).hasDerivAt.congr_deriv hderiv
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt G
      ((1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r)) r := by
    intro r _
    exact hGderiv r
  have hint : IntervalIntegrable
      (fun r : ℝ => (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r))
      volume 0 1 := by
    exact (by fun_prop : Continuous fun r : ℝ =>
      (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r)).intervalIntegrable 0 1
  have hpoly : EqOn cosineTauberianProfile
      (fun r : ℝ => 1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) (Set.uIcc 0 1) := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr
    exact cosineTauberianProfile_eq_poly hr'.1 hr'.2
  calc
    (∫ r in (0 : ℝ)..1,
      cosineTauberianProfile r * Real.cos (t * r)) =
        ∫ r in (0 : ℝ)..1,
          (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r) := by
            apply intervalIntegral.integral_congr
            intro r hr
            change cosineTauberianProfile r * Real.cos (t * r) =
              (1 / 6 - r ^ 2 / 2 + r ^ 3 / 3) * Real.cos (t * r)
            rw [hpoly hr]
    _ = G 1 - G 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = (2 * (1 - Real.cos t) - t * Real.sin t) / t ^ 4 := by
      simp only [G, mul_zero, Real.sin_zero, Real.cos_zero]
      norm_num
      field_simp [ne_of_gt ht]
      ring
    _ = cosineTauberianKernel t := by
      rw [cosineTauberianKernel_eq_quotient ht]

private theorem cosineTauberianKernel_neg (t : ℝ) :
    cosineTauberianKernel (-t) = cosineTauberianKernel t := by
  unfold cosineTauberianKernel
  apply intervalIntegral.integral_congr
  intro r _
  simp [Real.sinc_neg]

private theorem integrable_cosineTauberianKernel :
    Integrable cosineTauberianKernel := by
  have hneg : IntegrableOn cosineTauberianKernel (Iio (0 : ℝ)) := by
    have hcomp := integrableOn_cosineTauberianKernel.comp_neg
    have hset : -Ioi (0 : ℝ) = Iio 0 := by
      ext x
      simp
    rw [← hset]
    apply hcomp.congr_fun
    · intro x _
      exact cosineTauberianKernel_neg x
    · rw [hset]
      exact measurableSet_Iio
  have hrest : IntegrableOn cosineTauberianKernel
      (Iio (0 : ℝ) ∪ Ioi 0) := hneg.union integrableOn_cosineTauberianKernel
  have hzero : IntegrableOn cosineTauberianKernel ({0} : Set ℝ) :=
    integrableOn_singleton (by finiteness) (by simp)
  have hparts : Iio (0 : ℝ) ∪ Ioi 0 ∪ {0} = Set.univ := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · rcases lt_or_gt_of_ne hx with hlt | hgt
      · simp [hx]
      · simp [hx]
  have hfull : IntegrableOn cosineTauberianKernel Set.univ := by
    simpa [← hparts] using hrest.union hzero
  simpa using hfull.integrable

/-- The spline cosine transform agrees with the kernel at every nonzero
frequency. -/
private theorem intervalIntegral_cosineTauberianProfile_mul_cos_eq_kernel_of_ne
    {t : ℝ} (ht : t ≠ 0) :
    (∫ r in (0 : ℝ)..1,
      cosineTauberianProfile r * Real.cos (t * r)) = cosineTauberianKernel t := by
  by_cases htpos : 0 < t
  · exact intervalIntegral_cosineTauberianProfile_mul_cos_eq_kernel htpos
  · have htlt : t < 0 := (lt_or_gt_of_ne ht).resolve_right htpos
    have hneg : 0 < -t := neg_pos.mpr htlt
    have hcos : (∫ r in (0 : ℝ)..1,
        cosineTauberianProfile r * Real.cos (t * r)) =
        ∫ r in (0 : ℝ)..1,
          cosineTauberianProfile r * Real.cos ((-t) * r) := by
      apply intervalIntegral.integral_congr
      intro r _
      simp [neg_mul]
    calc
      (∫ r in (0 : ℝ)..1,
        cosineTauberianProfile r * Real.cos (t * r)) =
        ∫ r in (0 : ℝ)..1,
          cosineTauberianProfile r * Real.cos ((-t) * r) := hcos
      _ = cosineTauberianKernel (-t) :=
        intervalIntegral_cosineTauberianProfile_mul_cos_eq_kernel hneg
      _ = cosineTauberianKernel t := cosineTauberianKernel_neg t

private noncomputable def cosineTauberianComplexProfile (x : ℝ) : ℂ :=
  (cosineTauberianProfile x : ℂ)

private theorem cosineTauberianComplexProfile_continuous :
    Continuous cosineTauberianComplexProfile := by
  exact Complex.continuous_ofReal.comp continuous_cosineTauberianProfile

private noncomputable def cosineTauberianFourierIntegrand (t x : ℝ) : ℂ :=
  Complex.exp ((↑(-t * x) : ℂ) * Complex.I) * cosineTauberianComplexProfile x

private theorem cosineTauberianProfile_neg (x : ℝ) :
    cosineTauberianProfile (-x) = cosineTauberianProfile x := by
  simp [cosineTauberianProfile, abs_neg]

/-- The Fourier transform of the compact spline is twice the cosine kernel
away from the single frequency zero. -/
private theorem fourier_cosineTauberianComplexProfile_eq
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 cosineTauberianComplexProfile ξ =
      (2 * cosineTauberianKernel (2 * Real.pi * ξ) : ℂ) := by
  let t : ℝ := 2 * Real.pi * ξ
  let g : ℝ → ℂ := cosineTauberianFourierIntegrand t
  have htne : t ≠ 0 := by
    dsimp [t]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) hξ
  have hgcont : Continuous g := by
    change Continuous fun x : ℝ =>
      Complex.exp ((↑(-t * x) : ℂ) * Complex.I) *
        (cosineTauberianProfile x : ℂ)
    fun_prop [cosineTauberianProfile]
  have hfourier : 𝓕 cosineTauberianComplexProfile ξ = ∫ x : ℝ, g x := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g, cosineTauberianFourierIntegrand,
      cosineTauberianComplexProfile]
    congr 1
    congr 1
    simp only [starRingEnd_apply, star_trivial]
    push_cast
    dsimp [t]
    simp only [Complex.ofReal_mul]
    norm_num
    ring_nf
  have hgsupp : Function.support g ⊆ Ioc (-2 : ℝ) 2 := by
    apply Function.support_subset_iff'.2
    intro x hx
    have hx' : x ≤ -2 ∨ 2 < x := by
      by_contra h'
      have h'' := not_or.mp h'
      exact hx ⟨lt_of_not_ge h''.1, le_of_not_gt h''.2⟩
    have hax : 1 ≤ |x| := by
      rcases hx' with hleft | hright
      · rw [abs_of_neg (lt_of_le_of_lt hleft (by norm_num))]
        linarith
      · rw [abs_of_pos (by linarith : 0 < x)]
        linarith
    dsimp [g, cosineTauberianFourierIntegrand,
      cosineTauberianComplexProfile]
    rw [cosineTauberianProfile_zero_of_abs_ge hax]
    simp
  have hleftZero : (∫ x in (-2 : ℝ)..(-1), g x) = 0 := by
    calc
      (∫ x in (-2 : ℝ)..(-1), g x) = ∫ x in (-2 : ℝ)..(-1), 0 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (-2 : ℝ) (-1) := by
          simpa [Set.uIcc_of_le (by norm_num : (-2 : ℝ) ≤ -1)] using hx
        have hxle : x ≤ -1 := hx'.2
        have hax : 1 ≤ |x| := by
          rw [abs_of_nonpos (by linarith : x ≤ 0)]
          linarith
        dsimp [g, cosineTauberianFourierIntegrand,
          cosineTauberianComplexProfile]
        rw [cosineTauberianProfile_zero_of_abs_ge hax]
        simp
      _ = 0 := by simp
  have hrightZero : (∫ x in (1 : ℝ)..2, g x) = 0 := by
    calc
      (∫ x in (1 : ℝ)..2, g x) = ∫ x in (1 : ℝ)..2, 0 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (1 : ℝ) 2 := by
          simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hx
        have hxge : 1 ≤ x := hx'.1
        have hax : 1 ≤ |x| := by
          rw [abs_of_nonneg (by linarith : 0 ≤ x)]
          linarith
        dsimp [g, cosineTauberianFourierIntegrand,
          cosineTauberianComplexProfile]
        rw [cosineTauberianProfile_zero_of_abs_ge hax]
        simp
      _ = 0 := by simp
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hgcont.intervalIntegrable a b
  have houter : (∫ x in (-2 : ℝ)..2, g x) = ∫ x in (-1 : ℝ)..1, g x := by
    calc
      (∫ x in (-2 : ℝ)..2, g x) =
          (∫ x in (-2 : ℝ)..(-1), g x) + ∫ x in (-1 : ℝ)..2, g x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hint (-2) (-1)) (hint (-1) 2)).symm
      _ = ∫ x in (-1 : ℝ)..1, g x := by
        rw [hleftZero,
          ← intervalIntegral.integral_add_adjacent_intervals
            (hint (-1) 1) (hint 1 2), hrightZero]
        simp
  have hnegative : (∫ r in (-1 : ℝ)..0, g r) =
      ∫ r in (0 : ℝ)..1, g (-r) := by
    simpa using (intervalIntegral.integral_comp_neg (f := g)
      (a := (0 : ℝ)) (b := 1)).symm
  have hmiddle : (∫ r in (-1 : ℝ)..1, g r) =
      ∫ r in (0 : ℝ)..1, (g (-r) + g r) := by
    calc
      (∫ r in (-1 : ℝ)..1, g r) =
          (∫ r in (-1 : ℝ)..0, g r) + ∫ r in (0 : ℝ)..1, g r :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hint (-1) 0) (hint 0 1)).symm
      _ = (∫ r in (0 : ℝ)..1, g (-r)) + ∫ r in (0 : ℝ)..1, g r := by
        rw [hnegative]
      _ = ∫ r in (0 : ℝ)..1, (g (-r) + g r) := by
        exact (intervalIntegral.integral_add
          ((hgcont.comp (continuous_neg)).intervalIntegrable 0 1)
          (hint 0 1)).symm
  have hpair (r : ℝ) : g (-r) + g r =
      (2 * Real.cos (t * r) * cosineTauberianProfile r : ℂ) := by
    dsimp [g, cosineTauberianFourierIntegrand,
      cosineTauberianComplexProfile]
    rw [show -t * (-r) = t * r by ring,
      show -t * r = -(t * r) by ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp [Complex.ofReal_cos, Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, cosineTauberianProfile_neg]
    ring
  have hpairIntegral : (∫ r in (0 : ℝ)..1, (g (-r) + g r)) =
      (2 * cosineTauberianKernel t : ℂ) := by
    calc
      (∫ r in (0 : ℝ)..1, (g (-r) + g r)) =
          ∫ r in (0 : ℝ)..1,
            (2 * Real.cos (t * r) * cosineTauberianProfile r : ℂ) := by
              apply intervalIntegral.integral_congr
              intro r _
              exact hpair r
      _ = ↑(∫ r in (0 : ℝ)..1,
            2 * Real.cos (t * r) * cosineTauberianProfile r) :=
          by
            rw [show (fun r : ℝ =>
                (2 * Real.cos (t * r) * cosineTauberianProfile r : ℂ)) =
              fun r => ((2 * Real.cos (t * r) * cosineTauberianProfile r : ℝ) : ℂ)
              from by funext r; push_cast; ring]
            exact intervalIntegral.integral_ofReal
      _ = ↑(2 * ∫ r in (0 : ℝ)..1,
            cosineTauberianProfile r * Real.cos (t * r)) := by
          apply congrArg (fun z : ℝ => (z : ℂ))
          calc
            (∫ r in (0 : ℝ)..1,
                2 * Real.cos (t * r) * cosineTauberianProfile r) =
                ∫ r in (0 : ℝ)..1,
                  2 * (cosineTauberianProfile r * Real.cos (t * r)) := by
                    apply intervalIntegral.integral_congr
                    intro r _
                    ring
            _ = 2 * ∫ r in (0 : ℝ)..1,
                  cosineTauberianProfile r * Real.cos (t * r) := by
                    rw [intervalIntegral.integral_const_mul]
      _ = (2 * cosineTauberianKernel t : ℂ) := by
          rw [intervalIntegral_cosineTauberianProfile_mul_cos_eq_kernel_of_ne htne]
          norm_cast
  calc
    𝓕 cosineTauberianComplexProfile ξ = ∫ x : ℝ, g x := hfourier
    _ = ∫ x in (-2 : ℝ)..2, g x :=
      (intervalIntegral.integral_eq_integral_of_support_subset hgsupp).symm
    _ = ∫ x in (-1 : ℝ)..1, g x := houter
    _ = ∫ r in (0 : ℝ)..1, (g (-r) + g r) := hmiddle
    _ = (2 * cosineTauberianKernel t : ℂ) := hpairIntegral

private theorem integrable_fourier_cosineTauberianComplexProfile :
    Integrable (𝓕 cosineTauberianComplexProfile) := by
  have hscale : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hscaled : Integrable
      (fun ξ : ℝ => cosineTauberianKernel (2 * Real.pi * ξ)) :=
    (integrable_comp_mul_left_iff cosineTauberianKernel hscale).2
      integrable_cosineTauberianKernel
  have hscaledComplex0 : Integrable
      (fun ξ : ℝ => (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ)) :=
    hscaled.ofReal
  have hscaledComplex : Integrable
      (fun ξ : ℝ => (2 : ℂ) *
        (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ)) :=
    hscaledComplex0.const_mul 2
  have hEq : 𝓕 cosineTauberianComplexProfile =ᵐ[volume]
      fun ξ : ℝ => (2 : ℂ) *
        (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with ξ hξ
    exact fourier_cosineTauberianComplexProfile_eq hξ
  exact hscaledComplex.congr hEq.symm

private theorem inverse_fourier_cosineTauberianProfile (x : ℝ) :
    (∫ ξ : ℝ,
      Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
        ((2 : ℂ) * (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ))) =
      (cosineTauberianProfile x : ℂ) := by
  have hinv := cosineTauberianComplexProfile_continuous.fourierInv_fourier_eq
    cosineTauberianProfile_integrable.ofReal
    integrable_fourier_cosineTauberianComplexProfile
  have hinvx := congrFun hinv x
  have hInner (ξ : ℝ) : ⟪ξ, x⟫ = ξ * x := by
    exact Real.inner_apply ξ x
  have hExpand : (𝓕⁻ (𝓕 cosineTauberianComplexProfile)) x =
      ∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
          𝓕 cosineTauberianComplexProfile ξ := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [hInner ξ]
    simp only [smul_eq_mul]
    congr 1
    push_cast
    ring_nf
  have hInvIntegral :
      (∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
          𝓕 cosineTauberianComplexProfile ξ) =
        (cosineTauberianProfile x : ℂ) := by
    calc
      _ = (𝓕⁻ (𝓕 cosineTauberianComplexProfile)) x := hExpand.symm
    _ = (cosineTauberianProfile x : ℂ) := hinvx
  calc
    _ = ∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
          𝓕 cosineTauberianComplexProfile ξ := by
          apply integral_congr_ae
          filter_upwards
            [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with ξ hξ
          rw [← fourier_cosineTauberianComplexProfile_eq hξ]
    _ = (cosineTauberianProfile x : ℂ) := hInvIntegral

private noncomputable def cosineTauberianOscillator (x s : ℝ) : ℂ :=
  Complex.exp (↑(s * x) * Complex.I) * (cosineTauberianKernel s : ℂ)

private theorem integrable_cosineTauberianOscillator (x : ℝ) :
    Integrable (cosineTauberianOscillator x) := by
  have hKabs : Integrable (fun s : ℝ => |cosineTauberianKernel s|) := by
    simpa [Real.norm_eq_abs] using integrable_cosineTauberianKernel.norm
  have hmeas : AEStronglyMeasurable (cosineTauberianOscillator x) volume := by
    change AEStronglyMeasurable
      (fun s : ℝ => Complex.exp (↑(s * x) * Complex.I) *
        (cosineTauberianKernel s : ℂ)) volume
    have hExp : Continuous fun s : ℝ =>
        Complex.exp (↑(s * x) * Complex.I) := by fun_prop
    have hK : Continuous fun s : ℝ =>
        (cosineTauberianKernel s : ℂ) :=
      Complex.continuous_ofReal.comp continuous_cosineTauberianKernel
    have hcont : Continuous fun s : ℝ =>
        Complex.exp (↑(s * x) * Complex.I) *
          (cosineTauberianKernel s : ℂ) := hExp.mul hK
    exact hcont.aestronglyMeasurable
  have hbound : ∀ᵐ s : ℝ ∂volume,
      ‖cosineTauberianOscillator x s‖ ≤ |cosineTauberianKernel s| := by
    filter_upwards [] with s
    simp [cosineTauberianOscillator, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs]
  exact hKabs.mono' hmeas hbound

private theorem integral_cosineTauberianOscillator (x : ℝ) :
    (∫ s : ℝ, cosineTauberianOscillator x s) =
      (Real.pi : ℂ) * (cosineTauberianProfile x : ℂ) := by
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hcomp : (∫ ξ : ℝ, cosineTauberianOscillator x (c * ξ)) =
      |c⁻¹| • (∫ s : ℝ, cosineTauberianOscillator x s) :=
    MeasureTheory.Measure.integral_comp_mul_left
      (cosineTauberianOscillator x) c
  have hscaled :
      (∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
          ((2 : ℂ) * (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ))) =
        ((Real.pi : ℝ)⁻¹ : ℂ) *
          (∫ s : ℝ, cosineTauberianOscillator x s) := by
    calc
      _ = ∫ ξ : ℝ, (2 : ℂ) * cosineTauberianOscillator x (c * ξ) := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            dsimp [cosineTauberianOscillator, c]
            have harg : 2 * Real.pi * ξ * x = (2 * Real.pi * ξ) * x := by ring
            rw [harg]
            ring
      _ = (2 : ℂ) * ∫ ξ : ℝ, cosineTauberianOscillator x (c * ξ) :=
            integral_const_mul _ _
      _ = (2 : ℂ) *
          (|c⁻¹| • ∫ s : ℝ, cosineTauberianOscillator x s) := by rw [hcomp]
      _ = ((Real.pi : ℝ)⁻¹ : ℂ) *
          (∫ s : ℝ, cosineTauberianOscillator x s) := by
            rw [abs_of_nonneg (inv_nonneg.mpr hc.le), Complex.real_smul]
            dsimp [c]
            push_cast
            field_simp [Real.pi_ne_zero]
  have hInv := inverse_fourier_cosineTauberianProfile x
  have hcoeff : ((Real.pi : ℝ)⁻¹ : ℂ) *
      (∫ s : ℝ, cosineTauberianOscillator x s) =
        (cosineTauberianProfile x : ℂ) := by
    calc
      _ = ∫ ξ : ℝ,
          Complex.exp (↑(2 * Real.pi * ξ * x) * Complex.I) *
            ((2 : ℂ) * (cosineTauberianKernel (2 * Real.pi * ξ) : ℂ)) := hscaled.symm
      _ = (cosineTauberianProfile x : ℂ) := hInv
  have hπne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    (∫ s : ℝ, cosineTauberianOscillator x s) =
        (Real.pi : ℂ) *
          (((Real.pi : ℝ)⁻¹ : ℂ) *
            (∫ s : ℝ, cosineTauberianOscillator x s)) := by
          field_simp [hπne]
    _ = (Real.pi : ℂ) * (cosineTauberianProfile x : ℂ) := by rw [hcoeff]

private theorem integrable_cosineTauberianCosIntegrand (x : ℝ) :
    Integrable (fun s : ℝ => Real.cos (s * x) * cosineTauberianKernel s) := by
  have hKabs : Integrable (fun s : ℝ => |cosineTauberianKernel s|) := by
    simpa [Real.norm_eq_abs] using integrable_cosineTauberianKernel.norm
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => Real.cos (s * x) * cosineTauberianKernel s) volume := by
    have hcos : Continuous fun s : ℝ => Real.cos (s * x) := by fun_prop
    have hK : Continuous fun s : ℝ => cosineTauberianKernel s :=
      continuous_cosineTauberianKernel
    exact (hcos.mul hK).aestronglyMeasurable
  have hbound : ∀ᵐ s : ℝ ∂volume,
      ‖Real.cos (s * x) * cosineTauberianKernel s‖ ≤ |cosineTauberianKernel s| := by
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |Real.cos (s * x)| * |cosineTauberianKernel s| ≤
          1 * |cosineTauberianKernel s| :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ = |cosineTauberianKernel s| := by ring
  exact hKabs.mono' hmeas hbound

/-- The cosine transform of the Tauberian kernel on the full line. -/
theorem integral_cosineTauberianKernel_cos (x : ℝ) :
    (∫ s : ℝ, Real.cos (s * x) * cosineTauberianKernel s) =
      Real.pi * cosineTauberianProfile x := by
  have hcomplex := integral_cosineTauberianOscillator x
  have hosc := integrable_cosineTauberianOscillator x
  calc
    (∫ s : ℝ, Real.cos (s * x) * cosineTauberianKernel s) =
        ∫ s : ℝ, (cosineTauberianOscillator x s).re := by
          apply integral_congr_ae
          filter_upwards [] with s
          change Real.cos (s * x) * cosineTauberianKernel s =
            (Complex.exp (↑(s * x) * Complex.I) *
              (cosineTauberianKernel s : ℂ)).re
          rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    _ = ∫ s : ℝ, Complex.reCLM (cosineTauberianOscillator x s) := by
          simp only [Complex.reCLM_apply]
    _ = Complex.reCLM (∫ s : ℝ, cosineTauberianOscillator x s) := by
          exact ContinuousLinearMap.integral_comp_comm Complex.reCLM hosc
    _ = Real.pi * cosineTauberianProfile x := by
          rw [hcomplex]
          simp [Complex.ofReal_re]

/-- The half-line cosine transform of the Tauberian kernel. -/
theorem integral_Ioi_cosineTauberianKernel_cos (x : ℝ) :
    (∫ s in Ioi (0 : ℝ), Real.cos (s * x) * cosineTauberianKernel s) =
      (Real.pi / 2) * cosineTauberianProfile x := by
  let f : ℝ → ℝ := fun s => Real.cos (s * x) * cosineTauberianKernel s
  have hfint : Integrable f := by
    simpa [f] using integrable_cosineTauberianCosIntegrand x
  have heven (s : ℝ) : f (-s) = f s := by
    simp [f, Real.cos_neg, cosineTauberianKernel_neg, mul_neg]
  have hchange : (∫ s in Ioi (0 : ℝ), f (-s)) =
      ∫ s in Iio (0 : ℝ), f s := by
    let g : ℝ → ℝ := (Iio (0 : ℝ)).indicator f
    have hindicator (s : ℝ) : g (-s) = (Ioi (0 : ℝ)).indicator
        (fun y => f (-y)) s := by
      by_cases hs : 0 < s
      · simp [g, Set.indicator, hs]
      · have hs' : s ≤ 0 := le_of_not_gt hs
        simp [g, Set.indicator, hs, hs']
    have hleft : (∫ s : ℝ, g (-s)) = ∫ s in Ioi (0 : ℝ), f (-s) := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with s
      exact hindicator s
    have hright : (∫ s : ℝ, g s) = ∫ s in Iio (0 : ℝ), f s := by
      rw [integral_indicator measurableSet_Iio]
    have h := MeasureTheory.Measure.integral_comp_smul volume g (-1)
    simp only [smul_eq_mul, neg_one_mul] at h
    rw [hleft, hright] at h
    simpa [Module.finrank_self] using h
  have hneg : (∫ s in Ioi (0 : ℝ), f s) =
      ∫ s in Iio (0 : ℝ), f s := by
    calc
      (∫ s in Ioi (0 : ℝ), f s) = ∫ s in Ioi (0 : ℝ), f (-s) := by
        apply setIntegral_congr_ae measurableSet_Ioi
        filter_upwards [] with s _
        exact (heven s).symm
      _ = ∫ s in Iio (0 : ℝ), f s := hchange
  have hIci : (∫ s in Ici (0 : ℝ), f s) =
      ∫ s in Ioi (0 : ℝ), f s := by
    rw [← integral_indicator measurableSet_Ici,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with s hs
    by_cases hpos : 0 < s
    · simp [Set.indicator, hpos, le_of_lt hpos]
    · have hle : s ≤ 0 := le_of_not_gt hpos
      have hlt : s < 0 := lt_of_le_of_ne hle hs
      simp [Set.indicator, not_le_of_gt hlt, not_lt_of_ge (le_of_lt hlt)]
  have hsplit := integral_add_compl (s := Iio (0 : ℝ)) measurableSet_Iio hfint
  have hdouble :
      2 * (∫ s in Ioi (0 : ℝ), f s) = ∫ s : ℝ, f s := by
    calc
      2 * (∫ s in Ioi (0 : ℝ), f s) =
          (∫ s in Iio (0 : ℝ), f s) + ∫ s in Ici (0 : ℝ), f s := by
            rw [← hneg, ← hIci]
            ring
      _ = ∫ s : ℝ, f s := by simpa using hsplit
  have hfull : (∫ s : ℝ, f s) = Real.pi * cosineTauberianProfile x := by
    simpa [f] using integral_cosineTauberianKernel_cos x
  have hresult :
      2 * (∫ s in Ioi (0 : ℝ), f s) = Real.pi * cosineTauberianProfile x := by
    rw [hdouble, hfull]
  calc
    (∫ s in Ioi (0 : ℝ), f s) =
        (2 * (∫ s in Ioi (0 : ℝ), f s)) / 2 := by ring
    _ = (Real.pi * cosineTauberianProfile x) / 2 := by rw [hresult]
    _ = (Real.pi / 2) * cosineTauberianProfile x := by ring

/-- The kernel integral against `1 - cos` is the difference between the
Fourier profile at zero and at the specified frequency. -/
theorem integral_Ioi_one_sub_cos_mul_cosineTauberianKernel (x : ℝ) :
    (∫ s in Ioi (0 : ℝ),
      (1 - Real.cos (s * x)) * cosineTauberianKernel s) =
      (Real.pi / 2) *
        (cosineTauberianProfile 0 - cosineTauberianProfile x) := by
  have hK : IntegrableOn cosineTauberianKernel (Ioi (0 : ℝ)) :=
    by simpa [Real.cos_zero] using
      (integrable_cosineTauberianCosIntegrand (0 : ℝ)).integrableOn
  have hcos : IntegrableOn
      (fun s : ℝ => Real.cos (s * x) * cosineTauberianKernel s)
      (Ioi (0 : ℝ)) :=
    (integrable_cosineTauberianCosIntegrand x).integrableOn
  have hsub : IntegrableOn
      (fun s : ℝ => cosineTauberianKernel s -
        Real.cos (s * x) * cosineTauberianKernel s)
      (Ioi (0 : ℝ)) := hK.sub hcos
  have hpoint : (fun s : ℝ =>
      (1 - Real.cos (s * x)) * cosineTauberianKernel s) =
      fun s => cosineTauberianKernel s -
        Real.cos (s * x) * cosineTauberianKernel s := by
    funext s
    ring
  rw [hpoint, integral_sub hK hcos]
  have hzero := integral_Ioi_cosineTauberianKernel_cos (0 : ℝ)
  have hzero' : (∫ s in Ioi (0 : ℝ), cosineTauberianKernel s) =
      (Real.pi / 2) * cosineTauberianProfile 0 := by
    simpa [Real.cos_zero] using hzero
  rw [hzero', integral_Ioi_cosineTauberianKernel_cos x]
  ring

end ProbabilityTheory

end

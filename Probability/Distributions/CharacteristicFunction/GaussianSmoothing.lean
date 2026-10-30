/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Probability.Distributions.CharacteristicFunction.Symmetrization.Basic

/-!
# Gaussian smoothing of characteristic-function defects

## Public declarations

- `integral_gaussian_charFunDefect_eq_laplaceDefect` identifies the Gaussian
  average of $1-\operatorname{Re}\widehat\mu$ with the Laplace defect of
  $X^2$ for any probability law.
- `integral_gaussian_normCharFunDefect_eq_laplaceDefect` gives the corresponding
  identity for $1-|\widehat\mu|^2$ and the law of $X-X'$, with $X'$ an
  independent copy.

The Gaussian Fourier transform converts an averaged cosine defect into a
Laplace-transform defect. This gives a positive-kernel route for Tauberian
arguments about symmetric characteristic functions.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

private lemma gaussian_cos_two_pi (a : ℝ) :
    (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x)) =
      Real.exp (-Real.pi * a ^ 2) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (2 * Real.pi * a : ℝ) * (x : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  have hFourier := fourierIntegral_gaussian (b := (Real.pi : ℂ))
    (by simp [Real.pi_pos]) ((2 * Real.pi * a : ℝ) : ℂ)
  have hf : Integrable f volume := by
    have h := integrable_cexp_quadratic (b := (Real.pi : ℂ))
      (by simp [Real.pi_pos]) (c := Complex.I * (2 * Real.pi * a : ℝ)) (d := 0)
    convert h using 1 with x
    funext x
    dsimp [f]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfactor : (↑Real.pi / ↑Real.pi : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [div_self (by exact_mod_cast Real.pi_ne_zero)]
    simp
  have hexponent : -(↑(2 * Real.pi * a : ℝ)) ^ 2 / (4 * (Real.pi : ℂ)) =
      (↑(-Real.pi * a ^ 2) : ℂ) := by
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hreal : (∫ x, f x).re = Real.exp (-Real.pi * a ^ 2) := by
    rw [hFourier, hfactor, one_mul, hexponent, Complex.exp_ofReal_re]
  have hpoint (x : ℝ) :
      (f x).re = Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x) := by
    have harg : f x = Complex.exp
        (-(Real.pi * x ^ 2 : ℝ) + (2 * Real.pi * a * x : ℝ) * Complex.I) := by
      dsimp [f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hargRe :
        (-(Real.pi * x ^ 2 : ℝ) + (2 * Real.pi * a * x : ℝ) * Complex.I).re =
          -(Real.pi * x ^ 2) := by
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]
      ring
    have hargIm :
        (-(Real.pi * x ^ 2 : ℝ) + (2 * Real.pi * a * x : ℝ) * Complex.I).im =
          2 * Real.pi * a * x := by
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero]
      ring
    rw [harg, Complex.exp_re]
    rw [hargRe, hargIm]
    congr 2; ring
  calc
    (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x)) =
        ∫ x, (f x).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoint]
    _ = (∫ x, f x).re := integral_re hf
    _ = _ := hreal

/-- Averaging the cosine defect of a probability law against a Gaussian is
exactly the Laplace-transform defect of the squared variable. No moment
assumption is needed. -/
theorem integral_gaussian_charFunDefect_eq_laplaceDefect
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
      (1 - (charFun μ (2 * Real.pi * u * s)).re)) =
      ∫ x : ℝ, 1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2) ∂μ := by
  let f : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-Real.pi * p.1 ^ 2) * (1 - Real.cos (2 * Real.pi * u * p.1 * p.2))
  have hg : Integrable (fun s : ℝ => 2 * Real.exp (-Real.pi * s ^ 2)) volume := by
    simpa [mul_comm] using
      (integrable_exp_neg_mul_sq Real.pi_pos).const_mul (2 : ℝ)
  have hgprod : Integrable (fun p : ℝ × ℝ => 2 * Real.exp (-Real.pi * p.1 ^ 2))
      (volume.prod μ) := hg.comp_fst μ
  have hfmeas : AEStronglyMeasurable f (volume.prod μ) := by
    have hm : Measurable f := by
      dsimp [f]
      fun_prop
    exact hm.aestronglyMeasurable
  have hfbnd : ∀ p, ‖f p‖ ≤ 2 * Real.exp (-Real.pi * p.1 ^ 2) := by
    intro p
    have hcos0 : -1 ≤ Real.cos (2 * Real.pi * u * p.1 * p.2) := Real.neg_one_le_cos _
    have hcos1 : Real.cos (2 * Real.pi * u * p.1 * p.2) ≤ 1 := Real.cos_le_one _
    have he : 0 ≤ Real.exp (-Real.pi * p.1 ^ 2) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [f]
      nlinarith
    · exact mul_nonneg he (by linarith)
  have hf : Integrable f (volume.prod μ) := hgprod.mono' hfmeas (ae_of_all _ hfbnd)
  have hleft :
      (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
        cosineDefectIntegral μ (2 * Real.pi * u * s)) =
        ∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [cosineDefectIntegral, f]
    rw [integral_const_mul]
  have hdouble : (∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ) =
      ∫ x : ℝ, (∫ s : ℝ, f (s, x) ∂volume) ∂μ := by
    calc
      (∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ) =
          ∫ p : ℝ × ℝ, f p ∂(volume.prod μ) := (integral_prod f hf).symm
      _ = ∫ x : ℝ, (∫ s : ℝ, f (s, x) ∂volume) ∂μ := integral_prod_symm f hf
  have hinner (x : ℝ) :
      (∫ s : ℝ, f (s, x) ∂volume) = 1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2) := by
    have hgauss : Integrable (fun s : ℝ => Real.exp (-Real.pi * s ^ 2)) volume :=
      integrable_exp_neg_mul_sq Real.pi_pos
    have hcos : Integrable (fun s : ℝ =>
        Real.exp (-Real.pi * s ^ 2) * Real.cos (2 * Real.pi * (u * x) * s)) volume := by
      refine hgauss.mono' (by fun_prop) (ae_of_all _ fun s => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      calc
        Real.exp (-Real.pi * s ^ 2) * |Real.cos (2 * Real.pi * (u * x) * s)| ≤
            Real.exp (-Real.pi * s ^ 2) * 1 := by
              gcongr
              exact Real.abs_cos_le_one _
        _ = Real.exp (-Real.pi * s ^ 2) := by ring_nf
    have htotal : (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2)) = 1 := by
      simpa using gaussian_cos_two_pi (0 : ℝ)
    have hcosint := gaussian_cos_two_pi (u * x)
    have hrew : (fun s : ℝ => f (s, x)) = fun s =>
        Real.exp (-Real.pi * s ^ 2) -
          Real.exp (-Real.pi * s ^ 2) * Real.cos (2 * Real.pi * (u * x) * s) := by
      funext s
      dsimp [f]
      ring_nf
    rw [hrew, integral_sub hgauss hcos, htotal, hcosint]
    ring_nf
  calc
    _ = ∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ := by
      calc
        (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
            (1 - (charFun μ (2 * Real.pi * u * s)).re)) =
            ∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
              cosineDefectIntegral μ (2 * Real.pi * u * s) := by
                apply integral_congr_ae
                filter_upwards [] with s
                rw [← cosineDefectIntegral_eq_one_sub_charFun_re]
        _ = ∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ := hleft
    _ = ∫ x : ℝ, (∫ s : ℝ, f (s, x) ∂volume) ∂μ := hdouble
    _ = ∫ x : ℝ, (1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hinner x

/-- The Gaussian smoothing of the squared-modulus defect is the Laplace
defect of the symmetrized law. This is the form used for domain-of-attraction
Tauberian arguments. -/
theorem integral_gaussian_normCharFunDefect_eq_laplaceDefect
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (u : ℝ) :
    (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
      (1 - ‖charFun μ (2 * Real.pi * u * s)‖ ^ 2)) =
      ∫ x : ℝ, 1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2)
        ∂symmetrizedMeasure μ := by
  have hprob : IsProbabilityMeasure (symmetrizedMeasure μ) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  have h := @integral_gaussian_charFunDefect_eq_laplaceDefect
    (symmetrizedMeasure μ) hprob u
  calc
    (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
        (1 - ‖charFun μ (2 * Real.pi * u * s)‖ ^ 2)) =
        ∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) *
          (1 - (charFun (symmetrizedMeasure μ) (2 * Real.pi * u * s)).re) := by
            apply integral_congr_ae
            filter_upwards [] with s
            rw [charFun_symmetrizedMeasure_re]
    _ = ∫ x : ℝ, 1 - Real.exp (-Real.pi * u ^ 2 * x ^ 2)
          ∂symmetrizedMeasure μ := h

end ProbabilityTheory

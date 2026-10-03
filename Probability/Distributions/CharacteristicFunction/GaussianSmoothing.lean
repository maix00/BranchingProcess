/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Probability.Distributions.CharacteristicFunction.Symmetrization

/-!
# Gaussian smoothing of characteristic-function defects

The Gaussian Fourier transform converts an averaged cosine defect into a
Laplace-transform defect. This gives a positive-kernel route for Tauberian
arguments about symmetric characteristic functions.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

private theorem gaussian_cos_two_pi (a : ℝ) :
    (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x)) =
      Real.exp (-Real.pi * a ^ 2) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp (Complex.I * (2 * Real.pi * a : ℝ) * (x : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)
  have h := fourierIntegral_gaussian (b := (Real.pi : ℂ))
      (by simp [Real.pi_pos]) ((2 * Real.pi * a : ℝ) : ℂ)
  have hf : Integrable f volume := by
    have hbase := integrable_cexp_quadratic (b := (Real.pi : ℂ))
      (by simp [Real.pi_pos]) (c := Complex.I * (2 * Real.pi * a : ℝ)) (d := 0)
    have heq : f = fun x : ℝ => Complex.exp
        (-(Real.pi : ℂ) * (x : ℂ) ^ 2 +
          (Complex.I * (2 * Real.pi * a : ℝ)) * (x : ℂ) + 0) := by
      funext x
      dsimp [f]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    rw [heq]
    exact hbase
  have hreal : (∫ x, (f x).re) = Real.exp (-Real.pi * a ^ 2) := by
    calc
      (∫ x, (f x).re) = (∫ x, f x).re := integral_re hf
      _ = _ := by
        rw [h]
        have hfac : (↑Real.pi / ↑Real.pi : ℂ) ^ (1 / 2 : ℂ) = 1 := by
          rw [div_self (by exact_mod_cast Real.pi_ne_zero)]
          simp
        have hexpArg : -(↑(2 * Real.pi * a : ℝ)) ^ 2 / (4 * (Real.pi : ℂ)) =
            (↑(-Real.pi * a ^ 2) : ℂ) := by
          push_cast
          field_simp [Real.pi_ne_zero]
          ring_nf
        rw [hfac, hexpArg, one_mul, Complex.exp_ofReal_re]
  have hARe (x : ℝ) :
      (Complex.exp (Complex.I * (2 * Real.pi * a : ℝ) * (x : ℂ))).re =
        Real.cos (2 * Real.pi * a * x) := by
    rw [Complex.exp_re]
    simp [Complex.mul_re, Complex.I_re, Complex.I_im]
  have hAIm (x : ℝ) :
      (Complex.exp (Complex.I * (2 * Real.pi * a : ℝ) * (x : ℂ))).im =
        Real.sin (2 * Real.pi * a * x) := by
    rw [Complex.exp_im]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hBRe (x : ℝ) :
      (Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)).re =
        Real.exp (-Real.pi * x ^ 2) := by
    have harg : -(Real.pi : ℂ) * (x : ℂ) ^ 2 = (-(Real.pi * x ^ 2) : ℝ) := by
      push_cast
      ring_nf
    rw [harg, Complex.exp_ofReal_re]
    ring_nf
  have hBIm (x : ℝ) :
      (Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)).im = 0 := by
    have harg : -(Real.pi : ℂ) * (x : ℂ) ^ 2 = (-(Real.pi * x ^ 2) : ℝ) := by
      push_cast
      ring_nf
    rw [harg, Complex.exp_ofReal_im]
  have hpoint (x : ℝ) :
      (f x).re = Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x) := by
    dsimp [f]
    rw [Complex.mul_re, hARe, hAIm, hBRe, hBIm]
    ring_nf
  calc
    (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2) * Real.cos (2 * Real.pi * a * x)) =
        ∫ x, (f x).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hpoint]
    _ = Real.exp (-Real.pi * a ^ 2) := hreal

private noncomputable def cosineDefect (μ : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ x, 1 - Real.cos (t * x) ∂μ

private theorem cosineDefect_eq_one_sub_charFun_re
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cosineDefect μ t = 1 - (charFun μ t).re := by
  let f : ℝ → ℂ := fun x => Complex.exp (t * x * Complex.I)
  have hf : Integrable f μ := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    simp [f, Complex.norm_exp]
  have hcosInt : Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hcos : (∫ x : ℝ, Real.cos (t * x) ∂μ) = (charFun μ t).re := by
    rw [charFun_apply_real]
    calc
      (∫ x : ℝ, Real.cos (t * x) ∂μ) = ∫ x : ℝ, (f x).re ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [f]
        simp [Complex.exp_re]
      _ = (∫ x : ℝ, f x ∂μ).re := integral_re hf
  have huniv : (∫ _x : ℝ, (1 : ℝ) ∂μ) = 1 := by
    simp [Measure.real_def]
  rw [cosineDefect, integral_sub (integrable_const (1 : ℝ)) hcosInt, huniv, hcos]

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
      (∫ s : ℝ, Real.exp (-Real.pi * s ^ 2) * cosineDefect μ (2 * Real.pi * u * s)) =
        ∫ s : ℝ, ∫ x : ℝ, f (s, x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [cosineDefect, f]
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
              cosineDefect μ (2 * Real.pi * u * s) := by
                apply integral_congr_ae
                filter_upwards [] with s
                rw [← cosineDefect_eq_one_sub_charFun_re]
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

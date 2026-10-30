/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

import Analysis.Fourier.PositiveDefinite
import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import all Analysis.Fourier.Bochner.Lemmas.FejerApproximation

/-!
# Probability measure from an integrable positive-definite function

This internal stage establishes that, for continuous integrable positive-definite `ψ` with
`ψ 0 = 1`, the inverse-Fourier density `ρψ` is nonnegative and integrable, has total integral
`∫ ρψ = 1`, and satisfies `charFun ((ENNReal.ofReal ρψ) ∙ volume) ξ = ψ ξ`.
It then packages the density as a probability measure.

The declarations are proof support for `Analysis.Fourier.Bochner.Theorem`, not a reusable API.

## Internal proof declarations

- The private `exists_probMeasure_of_pd_integrable` constructs a probability
  measure $\mu$ from a continuous integrable positive-definite $\psi$ with
  $\psi(0)=1$, satisfying $\operatorname{charFun}(\mu,\xi)=\psi(\xi)$.
- The proof uses the density $\rho_\psi(x)=(2\pi)^{-1}
  \operatorname{Re}\int_{\mathbb R}\psi(u)e^{-ixu}\,du$, its nonnegativity,
  $\int_{\mathbb R}\rho_\psi(x)\,dx=1$, and Fourier inversion.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

/-- The inverse Fourier density is non-negative for PD + L¹ functions, as the pointwise
limit of non-negative Fejér approximants. -/
private lemma inverseFourierDensity_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (x : ℝ) : 0 ≤ inverseFourierDensity ψ x :=
  ge_of_tendsto (tendsto_fejerApproximant ψ hI x)
    (Eventually.of_forall fun n => fejerApproximant_nonneg ψ hψc hpd (↑n + 1) (by positivity) x)

/-- The inverse Fourier density is continuous (hence measurable) for continuous L¹ ψ.
Proof: the integrand `ψ(u) exp(-ixu)` is continuous in x, bounded by `‖ψ(u)‖ ∈ L¹`,
so by DCT the integral is continuous. -/
private lemma continuous_inverseFourierDensity (ψ : ℝ → ℂ)
    (hψc : Continuous ψ) (hI : Integrable ψ volume) :
    Continuous (inverseFourierDensity ψ) := by
  unfold inverseFourierDensity
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  -- The integral ∫ u, ψ u * exp(-ixu) is continuous in x : ℝ
  -- We use continuous_of_dominated with F(x, u) = ψ(u) * exp(-i·x·u)
  set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I)) with hG_def
  have hG_cont : Continuous fun x => ∫ u, G x u := by
    exact continuous_of_dominated
      (fun (x : ℝ) => by
        show AEStronglyMeasurable (fun u => ψ u * exp (-((x : ℂ) * ↑u * I))) volume
        exact (hψc.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
          continuous_const).neg.cexp)).aestronglyMeasurable)
      (fun x => ae_of_all _ fun u => by
        show ‖G x u‖ ≤ ‖ψ u‖
        simp only [G, norm_mul]
        rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one])
      hI.norm
      (ae_of_all _ fun u => by
        show Continuous fun (y : ℝ) => G y u
        simp only [G]
        refine Continuous.mul continuous_const (Complex.continuous_exp.comp ?_)
        exact ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const).neg)
  convert hG_cont using 1

/-- Bridge lemma: the Fourier transform of `w ↦ ψ(2πw)` (in the mathematician's convention)
equals `↑(inverseFourierDensity ψ y)` for PD integrable `ψ`. This uses that the FT integral
is real-valued by Hermitian symmetry, and changes variables `u = 2πw` in the integral. -/
private lemma fourierTransform_rescaled_eq (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (y : ℝ) :
    𝓕 (fun w => ψ (2 * Real.pi * w)) y = ↑(inverseFourierDensity ψ y) := by
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  -- Define the post-substitution integrand g u = exp(-iuy) * ψ u
  -- The key formula: 𝓕(ψ(2π·))(y) = (1/2π) * ∫ u, g(u)
  let g : ℝ → ℂ := fun u => Complex.exp (↑(-(u * y)) * Complex.I) * ψ u
  -- Step 1: Unfold 𝓕 to the exp-form
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  -- Goal: ∫ v, exp(↑(-2π·v·y)·I) * ψ(2π·v) = ↑(inverseFourierDensity ψ y)
  -- Step 2: Change variables u = 2πv using integral_comp_mul_left
  -- Rewrite integrand pointwise to expose g(2π·v)
  have heq_integrand : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * y) * Complex.I) * ψ (2 * Real.pi * v) =
      g (2 * Real.pi * v) := by
    intro v; simp only [g]
    congr 1; congr 1; push_cast; ring
  simp_rw [heq_integrand]
  -- Now apply integral_comp_mul_left and convert to a form involving ∫ u, g u
  -- Use suffices to avoid bound variable name issues with rw
  suffices h : |(2 * Real.pi)⁻¹| • ∫ u, g u = ↑(inverseFourierDensity ψ y) by
    calc ∫ v : ℝ, g (2 * Real.pi * v)
        = |(2 * Real.pi)⁻¹| • ∫ u, g u := Measure.integral_comp_mul_left g (2 * Real.pi)
      _ = ↑(inverseFourierDensity ψ y) := h
  rw [abs_inv, abs_of_pos h2pi_pos]
  -- Goal: (2π)⁻¹ • ∫ u, g u = ↑(inverseFourierDensity ψ y)
  -- Step 3: Show ∫ g is real using Hermitian symmetry of ψ
  have h_integral_im_zero : (∫ u, g u).im = 0 := by
    -- conj(g u) = g(-u) by Hermitian symmetry of ψ
    have h_conj_g : ∀ u : ℝ, conj (g u) = g (-u) := fun u => by
      simp only [g, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, conj_I, mul_neg]
      -- Goal: exp(-(↑(-(u*y))*I)) * conj(ψ u) = exp(↑(-(-u*y))*I) * ψ(-u)
      rw [← hpd.conj_neg u]
      -- Now: exp(-(↑(-(u*y))*I)) * conj(ψ u) = exp(↑(-(-u*y))*I) * conj(ψ u)
      congr 1
      -- Goal: exp(-(↑(-(u*y))*I)) = exp(↑(-(-u*y))*I)
      congr 1; push_cast; ring
    -- Show (∫ u, g u).im = 0 using conj(g u) = g(-u) and negation substitution.
    -- Key: ∫ g(-u) du = ∫ g u du, and ∫ conj(g) = ∫ g(-·) = ∫ g
    -- Hence Im(∫ g) = -Im(∫ g) → Im = 0.
    -- ∫ g(-u) du = ∫ g u du (substitution u ↦ -u)
    have h_neg_subst : ∫ u : ℝ, g (-u) = ∫ u : ℝ, g u := by
      have hfun : (fun u : ℝ => g (-u)) = fun u => g ((-1) * u) := by ext; simp
      rw [hfun, Measure.integral_comp_mul_left g (-1)]
      norm_num
    -- im(g u) = -im(g(-u)) since conj(g u) = g(-u) (and Im(conj z) = -Im z)
    have h_im_antisym : ∀ u : ℝ, Complex.im (g u) = -Complex.im (g (-u)) := fun u => by
      have heq := congr_arg Complex.im (h_conj_g u)
      simp only [conj_im] at heq
      linarith
    -- ∫ im(g u) = 0 by anti-symmetry: it equals its own negative
    have hint : ∫ u : ℝ, Complex.im (g u) = 0 := by
      -- ∫ im(g u) = ∫ -im(g(-u)) = -∫ im(g(-u)) = -∫ im(g u)
      -- Step 1: im(g u) = -im(g(-u))
      have heq1 : ∫ u : ℝ, Complex.im (g u) = ∫ u : ℝ, -Complex.im (g (-u)) := by
        congr 1; ext u; exact h_im_antisym u
      -- Step 2: ∫ im(g(-u)) = ∫ im(g u) via change-of-variables u ↦ -u
      have heq2 : ∫ u : ℝ, Complex.im (g (-u)) = ∫ u : ℝ, Complex.im (g u) := by
        have hfun : (fun u : ℝ => Complex.im (g (-u))) =
            fun u => (Complex.im ∘ g) ((-1) * u) := by ext; simp [Function.comp]
        rw [hfun, Measure.integral_comp_mul_left (Complex.im ∘ g) (-1)]
        norm_num
      have heq3 := integral_neg (f := fun u : ℝ => Complex.im (g (-u))) (μ := volume)
      linarith
    -- (∫ g).im = ∫ im(g) = 0
    have h_g_int_for_im : Integrable g volume := by
      apply Integrable.mono hI
      · show AEStronglyMeasurable (fun u : ℝ => Complex.exp (↑(-(u * y)) * I) * ψ u) volume
        exact ((Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.comp
            ((continuous_id.mul continuous_const).neg)).mul
            continuous_const))).mul hψc).aestronglyMeasurable
      · apply ae_of_all; intro u
        show ‖Complex.exp (↑(-(u * y)) * I) * ψ u‖ ≤ ‖ψ u‖
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h_im_eq : RCLike.im (∫ u : ℝ, g u) = 0 := by
      have key : ∫ u : ℝ, RCLike.im (g u) = RCLike.im (∫ u : ℝ, g u) :=
        integral_im h_g_int_for_im
      have hint' : (∫ u : ℝ, RCLike.im (g u)) = 0 := by exact_mod_cast hint
      linarith
    exact h_im_eq
  -- Step 4: Relate to inverseFourierDensity and finish
  unfold inverseFourierDensity
  push_cast
  -- The integral ∫ u, ψ u * exp(-iy·u) equals ∫ u, g u (just reordering factors)
  have h_eq_reorder : ∫ u : ℝ, ψ u * Complex.exp (-(↑y * ↑u * Complex.I)) =
      ∫ u : ℝ, g u := by
    congr 1; ext u; simp only [g]
    have hexpa : -(↑y * ↑u * Complex.I) = ↑(-(u * y)) * Complex.I := by push_cast; ring
    rw [hexpa, mul_comm]
  rw [h_eq_reorder]
  -- Since (∫ g).im = 0, write ∫ g = ↑(∫ g).re
  have h_int_re : (∫ u, g u) = ↑(∫ u, g u).re := by
    rw [Complex.ext_iff]; simp [h_integral_im_zero]
  rw [h_int_re]
  simp only [Complex.real_smul]
  push_cast [Complex.ofReal_re]
  rw [one_div]

set_option maxHeartbeats 800000 in
/-- Fubini + Gaussian Fourier identity:
`∫_x Re(∫_u ψ(u) exp(-ixu)) · exp(-x²/(2σ²)) = √(2πσ²) · Re(∫_u ψ(u) exp(-σ²u²/2))`.
This swaps the x and u integrals using Fubini, then evaluates the inner x-integral
via `fourierIntegral_gaussian`. -/
private lemma fubini_gaussianFourier_identity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hI : Integrable ψ volume) (σ2 : ℝ) (hσ2 : 0 < σ2) :
    ∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
      Real.exp (-(x ^ 2 / (2 * σ2))) =
    Real.sqrt (2 * Real.pi * σ2) *
      (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re := by
    -- Step 1: Re(z) * r = Re(z * ↑r)
    have hstep1 : ∀ x : ℝ,
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
          Real.exp (-(x ^ 2 / (2 * σ2))) =
        ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re := by
      intro x
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp_rw [hstep1]
    -- Step 2: ∫_x Re(f(x)) = Re(∫_x f(x)) by integral_re
    -- Need integrability of x ↦ (∫_u ψ exp(-ixu)) * ↑(exp(-x²/(2σ²)))
    have hψ_int_bdd : ∀ x : ℝ,
        ‖∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))‖ ≤ ∫ u, ‖ψ u‖ := by
      intro x
      calc ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖
          ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
        _ = ∫ u, ‖ψ u‖ := by
            congr 1; ext u; rw [norm_mul,
              show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
              norm_exp_ofReal_mul_I, mul_one]
    have hgauss_int : Integrable (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
      have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
      convert h using 1; ext x; congr 1; ring
    have hf_int : Integrable (fun x : ℝ =>
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume := by
      -- Bound: ‖f(x)‖ ≤ (∫ ‖ψ‖) * exp(-x²/(2σ²))
      apply (hgauss_int.const_mul (∫ u, ‖ψ u‖)).mono'
      · apply AEStronglyMeasurable.mul
        · -- x ↦ ∫ ψ(u) exp(-ixu) du is continuous (by continuous_of_dominated)
          -- hence AEStronglyMeasurable
          have hcont_param : Continuous (fun x : ℝ =>
              ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) := by
            set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I))
            exact continuous_of_dominated
              (fun (x : ℝ) => (hψc.mul ((((continuous_ofReal.comp continuous_const).mul
                continuous_ofReal).mul continuous_const).neg.cexp)).aestronglyMeasurable)
              (fun x => ae_of_all _ fun u => by
                show ‖G x u‖ ≤ ‖ψ u‖
                simp only [G, norm_mul]
                rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                  norm_exp_ofReal_mul_I, mul_one])
              hI.norm
              (ae_of_all _ fun u => by
                show Continuous fun (y : ℝ) => G y u
                simp only [G]
                refine Continuous.mul continuous_const (Complex.continuous_exp.comp ?_)
                exact ((Complex.continuous_ofReal.mul continuous_const).mul
                  continuous_const).neg)
          exact hcont_param.aestronglyMeasurable
        · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
            (continuous_neg.comp ((continuous_pow 2).div_const _)))).aestronglyMeasurable
      · exact ae_of_all _ fun x => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
          exact mul_le_mul_of_nonneg_right (hψ_int_bdd x) (Real.exp_nonneg _)
    -- ∫ Re(f(x)) = Re(∫ f(x))
    conv_lhs =>
      arg 2; ext x
      rw [show ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
        Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) from rfl]
    rw [show (fun x : ℝ => Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
      (fun x : ℝ => RCLike.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) from rfl,
      integral_re hf_int]
    -- Prove the complex identity, then take .re
    suffices hcomplex : (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
        ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
      ↑(Real.sqrt (2 * Real.pi * σ2)) *
        ∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))) by
      show (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
        Real.sqrt (2 * Real.pi * σ2) *
          (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
      rw [hcomplex]
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    -- Pull ↑exp inside the inner integral
    have hpull : ∀ x : ℝ,
        (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
        ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) := by
      intro x; exact (integral_mul_const _ _).symm
    simp_rw [hpull]
    -- Product integrability for Fubini
    have hcont_prod : Continuous (fun p : ℝ × ℝ =>
        ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
          ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) :=
      ((hψc.comp continuous_snd).mul
        (Complex.continuous_exp.comp
          (((continuous_ofReal.comp continuous_fst).mul
            (continuous_ofReal.comp continuous_snd)).mul
            continuous_const).neg)).mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_neg.comp ((continuous_pow 2 |>.comp continuous_fst).div_const _))))
    have hprod_int : Integrable (fun p : ℝ × ℝ =>
        ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
          ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (volume.prod volume) := by
      rw [integrable_prod_iff hcont_prod.aestronglyMeasurable]
      refine ⟨?_, ?_⟩
      · exact ae_of_all _ fun x => by
          show Integrable (fun u => ψ u * exp (-(↑x * ↑u * I)) *
            ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume
          apply Integrable.mono' (hI.norm.mul_const (Real.exp (-(x ^ 2 / (2 * σ2)))))
          · exact (hcont_prod.comp
              (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          · exact ae_of_all _ fun u => by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.exp_nonneg _),
                show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I, mul_one]
      · have hnorm_eq : (fun x => ∫ u, ‖(fun p : ℝ × ℝ => ψ p.2 *
            exp (-(↑p.1 * ↑p.2 * I)) *
              ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (x, u)‖) =
            fun x => (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2))) := by
          ext x
          show ∫ u, ‖ψ u * exp (-(↑x * ↑u * I)) *
            ↑(Real.exp (-(x ^ 2 / (2 * σ2))))‖ =
            (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2)))
          simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
          rw [← integral_mul_const]
          congr 1; ext u
          rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
            norm_exp_ofReal_mul_I, mul_one]
        rw [hnorm_eq]
        exact hgauss_int.const_mul _
    -- Apply Fubini
    rw [integral_integral_swap hprod_int]
    -- Evaluate the inner x-integral for each u
    have hinner_eq : ∀ u : ℝ,
        (∫ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
        ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
          ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) := by
      intro u
      have hassoc : ∀ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
        ψ u * (exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) := fun x => by ring
      simp_rw [hassoc]
      rw [show (∫ x : ℝ, ψ u * (exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
        ψ u * ∫ x : ℝ, exp (-(↑x * ↑u * I)) *
          ↑(Real.exp (-(x ^ 2 / (2 * σ2))))
        from integral_const_mul _ _]
      congr 1
      -- Evaluate via fourierIntegral_gaussian
      have hrw : ∀ x : ℝ,
          exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
          cexp (I * (-↑u) * ↑x) *
            cexp (-(↑(1 / (2 * σ2)) : ℂ) * (↑x) ^ 2) := by
        intro x
        congr 1
        · congr 1; ring
        · rw [Complex.ofReal_exp]; congr 1; push_cast; ring
      simp_rw [hrw]
      have hb_re : (0 : ℝ) < (↑(1 / (2 * σ2)) : ℂ).re := by
        simp [Complex.ofReal_re]; positivity
      rw [fourierIntegral_gaussian hb_re (-↑u)]
      have h1 : (↑(1 / (2 * σ2)) : ℂ) = 1 / (2 * ↑σ2) := by push_cast; ring
      rw [h1]
      have h2piσ_nn : (0 : ℝ) ≤ 2 * Real.pi * σ2 := by positivity
      have hbase : (↑Real.pi : ℂ) / (1 / (2 * ↑σ2)) = ↑(2 * Real.pi * σ2) := by
        push_cast; field_simp
      rw [hbase, show (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) from by push_cast; ring,
        ← ofReal_cpow h2piσ_nn,
        show (2 * Real.pi * σ2) ^ (1 / 2 : ℝ) = Real.sqrt (2 * Real.pi * σ2) from
          (Real.sqrt_eq_rpow _).symm]
      congr 1
      rw [Complex.ofReal_exp]; congr 1
      push_cast
      have hσ2_ne : (↑σ2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hσ2)
      field_simp; ring
    -- Rewrite inner integrals and finish
    simp_rw [hinner_eq]
    simp_rw [show ∀ u : ℝ, ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
        ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) =
      ↑(Real.sqrt (2 * Real.pi * σ2)) * (ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))))
      from fun u => by ring]
    exact integral_const_mul _ _

set_option maxHeartbeats 800000 in
/-- Each Gaussian-smoothed lintegral satisfies `∫⁻ ρ(x) exp(-x²/(2σ²)) ≤ 1`.
Uses the Fubini identity, `‖ψ‖ ≤ 1`, and `∫ exp(-σ²u²/2) = √(2π/σ²)`. -/
private lemma gaussianSmoothed_lintegral_le_one (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1)
    (hI : Integrable ψ volume) (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hρ_nn : ∀ x, 0 ≤ inverseFourierDensity ψ x) :
    ∫⁻ x, ENNReal.ofReal (inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2)))) ∂volume ≤ 1 := by
  have hρ_cont := continuous_inverseFourierDensity ψ hψc hI
  have hgn_nn : ∀ x, 0 ≤ inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2))) :=
    fun x => mul_nonneg (hρ_nn x) (Real.exp_nonneg _)
  -- ρ is bounded
  have hρ_bdd : ∃ C, ∀ x, inverseFourierDensity ψ x ≤ C := by
    use (1 / (2 * Real.pi)) * ∫ u, ‖ψ u‖
    intro x
    unfold inverseFourierDensity
    apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le
      (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos).le)
    calc (∫ u, ψ u * exp (-(↑x * ↑u * I))).re
        ≤ |(∫ u, ψ u * exp (-(↑x * ↑u * I))).re| := le_abs_self _
      _ ≤ ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖ := abs_re_le_norm _
      _ ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
      _ = ∫ u, ‖ψ u‖ := by
          congr 1; ext u; rw [norm_mul,
            show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
            norm_exp_ofReal_mul_I, mul_one]
  -- The product is integrable (bounded × Gaussian)
  have hgn_integrable : Integrable (fun x => inverseFourierDensity ψ x *
      Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
    -- Gaussian is integrable
    have hgauss_cont : Continuous (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) :=
      Real.continuous_exp.comp (continuous_neg.comp
        ((continuous_pow 2).div_const _))
    have hgauss_int : Integrable (fun x : ℝ =>
        Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
      have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
      convert h using 1; ext x; congr 1; ring
    -- ρ is bounded, so ρ * Gaussian is integrable
    obtain ⟨C, hC⟩ := hρ_bdd
    exact hgauss_int.bdd_mul hρ_cont.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ_nn x)]; exact hC x)
  -- Convert ∫⁻ to ∫
  rw [← ofReal_integral_eq_lintegral_ofReal hgn_integrable (ae_of_all _ hgn_nn)]
  rw [ENNReal.ofReal_le_one]
  -- Goal: ∫ ρ(x) * exp(-x²/(2σ²)) dx ≤ 1
  -- We unfold ρ and bound using |ψ| ≤ 1 and norm_integral_le_integral_norm.
  -- The bound ρ(x) ≤ (1/(2π)) * ∫ ‖ψ(u)‖ du is too loose (grows with σ).
  -- Instead, we use a Fubini argument to swap the x and u integrals.
  -- ∫_x ρ(x) exp(-x²/(2σ²)) dx = (σ/√(2π)) Re ∫_u ψ(u) exp(-σ²u²/2) du
  -- ≤ (σ/√(2π)) ∫ exp(-σ²u²/2) du = 1.
  -- The Fubini swap + Gaussian FT evaluation is proved via fourierIntegral_gaussian.
  have hψ_norm_le : ∀ u, ‖ψ u‖ ≤ 1 := hpd.norm_le_one h0
  -- ∫ ρ(x) exp(-x²/(2σ²)) dx = (σ/√(2π)) Re ∫ ψ(u) exp(-σ²u²/2) du
  have gaussian_fubini_bound :
      ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2))) ≤
      Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
      ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
    -- By Fubini + fourierIntegral_gaussian:
    -- ∫_x (∫_u ψ(u) exp(-ixu)).re * exp(-x²/(2σ²))
    -- = √(2πσ²) Re ∫_u ψ(u) exp(-σ²u²/2)
    -- ≤ √(2πσ²) ∫_u ‖ψ(u)‖ exp(-σ²u²/2)
    -- So the bound = (1/(2π)) * √(2πσ²) * ∫ ‖ψ‖ exp(...)
    -- = √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2).
    have fubini_identity := fubini_gaussianFourier_identity ψ hψc hI σ2 hσ2
    -- Unfold ρ and pull out 1/(2π)
    have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    -- LHS = (1/(2π)) * ∫ Re(∫ ψ exp(-ixu)) * exp(-x²/(2σ²))
    have hLHS_eq : ∫ x, inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2))) =
      1 / (2 * Real.pi) * (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
        Real.exp (-(x ^ 2 / (2 * σ2)))) := by
      simp_rw [inverseFourierDensity, mul_assoc]
      rw [integral_const_mul]
    rw [hLHS_eq, fubini_identity]
    -- Goal: (1/(2π)) * (√(2πσ²) * Re(∫ ψ exp(-σ²u²/2)))
    --     ≤ √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2)
    have hRe_le : (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re ≤
        ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
      calc (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
          ≤ ‖∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
            le_trans (le_abs_self _) (abs_re_le_norm _)
        _ ≤ ∫ u : ℝ, ‖ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
            congr 1; ext u
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.exp_nonneg _)]
    -- Simplify the constant: (1/(2π)) * √(2πσ²) = √σ²/√(2π)
    -- After rw hLHS_eq and fubini_identity, goal is:
    -- 1/(2π) * (√(2πσ²) * Re(∫ ψ exp(-σ²u²/2))) ≤ √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2)
    -- Bound Re ≤ ‖·‖ ≤ ∫ ‖·‖, simplify constant.
    set I_re := (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
    set I_norm := ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2))
    have hI_norm_nn : 0 ≤ I_norm :=
      integral_nonneg fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
    have hI_re_le_norm : I_re ≤ I_norm := hRe_le
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hpi_pos
    have hsqrt_nn : 0 ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
    -- The constant: 1/(2π) * √(2πσ²) = √σ²/√(2π)
    have hc_eq : 1 / (2 * Real.pi) * Real.sqrt (2 * Real.pi * σ2) =
        Real.sqrt σ2 / Real.sqrt (2 * Real.pi) := by
      rw [show (2 * Real.pi * σ2) = (2 * Real.pi) * σ2 from by ring,
        Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
      -- Goal: 1/(2π) * (√(2π) * √σ2) = √σ2/√(2π)
      have h := ne_of_gt hsqrt_pos
      field_simp
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    -- Goal: 1/(2π) * (√(2πσ²) * I_re) ≤ √σ²/√(2π) * I_norm
    -- = hc_eq ▸ √σ²/√(2π) * I_re ≤ √σ²/√(2π) * I_norm
    have h1 : 1 / (2 * Real.pi) * (Real.sqrt (2 * Real.pi * σ2) * I_re)
      = Real.sqrt σ2 / Real.sqrt (2 * Real.pi) * I_re := by
      rw [← hc_eq]; ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hI_re_le_norm
      (div_nonneg hsqrt_nn hsqrt_pos.le)
  -- Now bound the RHS
  calc ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2)))
      ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
        ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := gaussian_fubini_bound
    _ ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
        ∫ u, Real.exp (-(σ2 * u ^ 2 / 2)) := by
        have hexp_int : Integrable (fun u : ℝ =>
            Real.exp (-(σ2 * u ^ 2 / 2))) volume := by
          apply (integrable_exp_neg_mul_sq (by positivity : 0 < σ2 / 2)).mono'
            (by fun_prop)
          exact ae_of_all _ fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
            apply Real.exp_le_exp_of_le; linarith [sq_nonneg u]
        apply mul_le_mul_of_nonneg_left
        · apply integral_mono_of_nonneg
          · exact ae_of_all _ fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
          · exact hexp_int
          · exact ae_of_all _ fun u =>
              mul_le_of_le_one_left (Real.exp_nonneg _) (hψ_norm_le u)
        · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 1 := by
        -- ∫ exp(-σ²u²/2) du = √(2π/σ²) = √(2π)/√σ², so the product = 1.
        -- Rewrite the integral using integral_gaussian
        -- ∫ exp(-σ2 u²/2) du = √(2π/σ2), so √σ2/√(2π) * √(2π/σ2) = 1.
        have h_int_eq : (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2))) =
            Real.sqrt (2 * Real.pi / σ2) := by
          have h1 := integral_gaussian (σ2 / 2)
          -- h1 : ∫ x, exp(-(σ2/2) * x²) = √(π/(σ2/2))
          -- We need: ∫ u, exp(-(σ2 * u²/2)) = √(2π/σ2)
          -- The integrands are equal: -(σ2/2)*x² = -(σ2*x²/2)
          -- The RHS: π/(σ2/2) = 2π/σ2
          calc (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2)))
              = ∫ u : ℝ, Real.exp (-(σ2 / 2) * u ^ 2) := by
                congr 1; ext u; congr 1; ring
            _ = Real.sqrt (Real.pi / (σ2 / 2)) := h1
            _ = Real.sqrt (2 * Real.pi / σ2) := by
                congr 1; field_simp
        rw [h_int_eq, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi),
          div_mul_div_comm, mul_comm (Real.sqrt σ2) (Real.sqrt (2 * Real.pi)),
          div_self (ne_of_gt (mul_pos (Real.sqrt_pos.mpr
            (by positivity : 0 < 2 * Real.pi)) (Real.sqrt_pos.mpr hσ2)))]

set_option maxHeartbeats 800000 in
/-- The inverseFourierDensity is integrable for PD+continuous+L¹ functions.
Proof: ρ ≥ 0 (from Fejér argument) and the Gaussian regularization shows ∫ ρ = 1. -/
private lemma integrable_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    Integrable (inverseFourierDensity ψ) volume := by
  -- ρ ≥ 0 (from inverseFourierDensity_nonneg, which uses Fejér ≥ 0)
  have hρ_nn := inverseFourierDensity_nonneg ψ hψc hpd hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc hI
  have hρ_meas : AEStronglyMeasurable (inverseFourierDensity ψ) volume :=
    hρ_cont.aestronglyMeasurable
  -- Strategy: show ∫⁻ ρ ≤ 1 < ∞ using MCT + Gaussian regularization.
  -- Step 1: Define the Gaussian-truncated functions gₙ(x) = ρ(x) · exp(-x²/(2(n+1))).
  -- These are integrable (bounded × Gaussian) and monotonically increase to ρ.
  -- Step 2: Show ∫ gₙ → 1 via Gaussian FT + DCT.
  -- Step 3: By MCT, ∫⁻ ρ = sup ∫⁻ gₙ ≤ 1 < ∞, hence ρ ∈ L¹.
  apply (lintegral_ofReal_ne_top_iff_integrable hρ_meas (ae_of_all _ hρ_nn)).mp
  -- Goal: ∫⁻ x, ENNReal.ofReal (ρ x) ∂volume ≠ ⊤
  -- Use MCT: gₙ ↗ ρ, so ∫⁻ ρ = sup ∫⁻ gₙ. Each ∫ gₙ ≤ 1 (from the Gaussian computation).
  -- Hence ∫⁻ ρ ≤ 1 < ⊤.
  -- Define the approximating sequence
  set gn : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * (↑n + 1)))))
  -- gn is monotone increasing to ENNReal.ofReal (ρ x)
  have hgn_mono : ∀ᵐ x ∂volume, Monotone (fun n => gn n x) := by
    apply ae_of_all; intro x m n hmn
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp_of_le
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg x)
      · linarith [show (0 : ℝ) ≤ ↑n from Nat.cast_nonneg n]
      · linarith [show (0 : ℝ) ≤ ↑m from Nat.cast_nonneg m,
                   show (↑m : ℝ) ≤ ↑n from Nat.cast_le.mpr hmn]
    · exact hρ_nn x
  have hgn_tendsto : ∀ᵐ x ∂volume, Tendsto (fun n => gn n x) atTop
      (𝓝 (ENNReal.ofReal (inverseFourierDensity ψ x))) := by
    apply ae_of_all; intro x
    apply ENNReal.tendsto_ofReal
    conv_rhs => rw [show inverseFourierDensity ψ x =
      inverseFourierDensity ψ x * 1 from (mul_one _).symm]
    apply Tendsto.mul tendsto_const_nhds
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact (Real.continuous_exp.tendsto 0).comp (by
      -- Goal: -(x²/(2(n+1))) → 0
      have : Tendsto (fun n : ℕ => x ^ 2 / (2 * (↑n + 1))) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds
          ((Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
            (by norm_num : (0 : ℝ) < 2))
      simpa using this.neg)
  have hgn_meas : ∀ n, AEMeasurable (gn n) volume := by
    intro n
    exact (hρ_cont.mul (Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_pow 2).div_const _)))).measurable.ennreal_ofReal.aemeasurable
  -- By MCT: ∫⁻ ρ = lim ∫⁻ gₙ
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hgn_meas hgn_mono hgn_tendsto
  -- Each ∫⁻ gₙ = ENNReal.ofReal (∫ gₙ_real) since gₙ_real ≥ 0
  -- And ∫ gₙ_real → 1 by Gaussian FT + DCT (the hard computation).
  -- So ∫⁻ ρ = ENNReal.ofReal 1 ≠ ⊤.
  -- For now, we show ∫⁻ ρ < ⊤ by showing the limit is finite.
  have hgn_le_one : ∀ n, ∫⁻ x, gn n x ∂volume ≤ 1 := by
    intro n
    set σ2 : ℝ := ↑n + 1 with hσ2_def
    have hσ2_pos : 0 < σ2 := by positivity
    rw [show gn n = fun x => ENNReal.ofReal (inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2)))) from by ext x; simp [gn, hσ2_def]]
    exact gaussianSmoothed_lintegral_le_one ψ hψc hpd h0 hI σ2 hσ2_pos hρ_nn
  have hbdd : ∫⁻ x, ENNReal.ofReal (inverseFourierDensity ψ x) ∂volume ≤ 1 :=
    le_of_tendsto' hMCT hgn_le_one
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hbdd

set_option maxHeartbeats 800000 in
/-- The characteristic function of the measure with density `inverseFourierDensity ψ`
equals `ψ`, assuming `ψ` is continuous and L¹. This is the Fourier inversion theorem
specialized to the probabilist convention. -/
private lemma charFun_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) (ξ : ℝ) :
    ∫ x, (inverseFourierDensity ψ x : ℝ) • exp (↑ξ * ↑x * I) = ψ ξ := by
  -- Proof via Fourier inversion theorem (mathlib).
  -- Define the rescaled function f(w) = ψ(2πw).
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  set f : ℝ → ℂ := fun w => ψ (2 * Real.pi * w) with hf_def
  have hf_int : Integrable f volume := by
    show Integrable (fun w => ψ (2 * Real.pi * w)) volume
    exact hI.comp_mul_left' h2pi_ne
  have hf_cont : Continuous f := hψc.comp (continuous_const.mul continuous_id)
  -- 𝓕 f = ↑ ∘ inverseFourierDensity ψ
  have hFf_eq : ∀ y, 𝓕 f y = ↑(inverseFourierDensity ψ y) :=
    fourierTransform_rescaled_eq ψ hψc hpd hI
  -- 𝓕 f is integrable (from ρ ≥ 0 + Gaussian regularization)
  have hFf_int : Integrable (𝓕 f) volume := by
    rw [show 𝓕 f = fun y => (↑(inverseFourierDensity ψ y) : ℂ) from funext hFf_eq]
    exact (integrable_inverseFourierDensity ψ hψc hpd h0 hI).ofReal
  -- Apply Fourier inversion: 𝓕⁻(𝓕 f)(v) = f(v) for all v.
  have hinv := hf_cont.fourierInv_fourier_eq hf_int hFf_int
  -- Evaluate at v = ξ/(2π)
  set v := ξ / (2 * Real.pi) with hv_def
  have hfv : f v = ψ ξ := by
    simp only [hf_def, hv_def, mul_div_cancel₀ _ h2pi_ne]
  -- hinv says 𝓕⁻(𝓕 f) = f, so 𝓕⁻(𝓕 f)(v) = ψ(ξ)
  have hinv_v := congr_fun hinv v
  rw [hfv] at hinv_v
  -- 𝓕⁻(𝓕 f)(v) = ∫ exp(2πi⟪y,v⟫) (𝓕 f)(y) dy = ∫ exp(2πi y ξ/(2π)) ↑(ρ(y)) dy
  -- = ∫ exp(iξy) ↑(ρ(y)) dy = ∫ ↑(ρ(y)) • exp(iξy) dy
  -- This equals our goal.
  rw [← hinv_v]
  -- Now show 𝓕⁻(𝓕 f)(v) = ∫ (inverseFourierDensity ψ x) • exp(iξx) dx
  -- 𝓕⁻(𝓕 f)(v) = ∫ y, 𝐞(⟪y,v⟫) • (𝓕 f)(y) = ∫ y, exp(2πi y v) • ↑(ρ(y))
  -- Since v = ξ/(2π): exp(2πi y v) = exp(iξy), so integrand = ↑(ρ(y)) • exp(iξy)
  -- Change of inner product convention: ⟪y,v⟫ = y*v on ℝ, so 2π⟪y,v⟫ = 2πyξ/(2π) = ξy.
  -- Convention bridge: 𝓕⁻(𝓕 f)(v) uses exp(2πi⟪y,v⟫) and our goal uses exp(iξy).
  -- Since v = ξ/(2π) and ⟪y,v⟫ = y·v on ℝ: 2π·y·ξ/(2π) = ξ·y.
  -- So the integrands match after this simplification.
  rw [Real.fourierInv_eq']
  simp_rw [hFf_eq]
  -- The integrands match: exp(2πi⟪y,v⟫) • ↑(ρ(y)) = ↑(ρ(y)) • exp(iξy)
  -- since ⟪y,v⟫ = y·v = y·ξ/(2π) on ℝ, so 2π⟪y,v⟫ = ξy.
  -- Both sides equal ↑(ρ(y)) * exp(iξy) after commuting the scalar mul.
  -- The integrands are equal after simplifying the inner product on ℝ:
  -- ⟪y,v⟫ = y*v, 2π*y*v = 2π*y*ξ/(2π) = ξ*y, so exp terms match.
  -- The scalar multiplication commutes: 𝐞(t) • ↑r = ↑r • 𝐞(t) since ℂ is commutative.
  congr 1; ext y
  -- Both sides equal ↑(ρ(y)) * cexp(↑ξ * ↑y * I).
  -- LHS: 𝐞(⟪y,v⟫) • ↑(ρ(y)) = cexp(2πi⟪y,v⟫) * ↑(ρ(y))
  -- with ⟪y,v⟫ = y*v = y*ξ/(2π), so 2π⟪y,v⟫ = ξy.
  -- RHS: ↑(ρ(y)) • cexp(↑ξ * ↑y * I) = ↑(ρ(y)) * cexp(↑ξ * ↑y * I)
  -- These are equal by commutativity of multiplication.
  simp only [Complex.real_smul, hv_def, Complex.ofReal_mul]
  -- Goal: cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2) * ↑(ρ y) = ↑(ρ y) * cexp (↑ξ * ↑y * I)
  rw [mul_comm]
  -- Goal: ↑(ρ y) * cexp (↑ξ * ↑y * I) = ↑(ρ y) * cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2)
  congr 1
  -- Goal: cexp (↑ξ * ↑y * I) = cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2)
  -- Both sides are exp(i * ξ * y) up to reordering.
  congr 1
  -- Goal: ↑ξ * ↑y * I = I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2
  -- Key: ⟪y, c⟫_ℝ = c * y on ℝ.
  -- After rewriting the inner product, reduce to ring.
  -- Goal: ↑ξ * ↑y * I = ↑2 * ↑π * ↑⟪y, ξ / (2 * π)⟫ * I
  -- Compute ⟪y, c⟫ = c * y on ℝ (using RCLike inner product).
  have hInner : ⟪y, ξ / (2 * Real.pi)⟫ = ξ / (2 * Real.pi) * y := by
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial]
    exact AddMonoidHom.id_apply (M := ℝ) _
  -- Cast to ℂ, substitute hInner, then ring.
  have hCast : (↑⟪y, ξ / (2 * Real.pi)⟫ : ℂ) = ↑ξ / ↑(2 * Real.pi) * ↑y := by
    push_cast [hInner]; ring
  rw [hCast]
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The inverse Fourier density integrates to 1 when `ψ(0) = 1`.
Derived from `charFun_inverseFourierDensity` at `ξ = 0`. -/
private lemma integral_inverseFourierDensity_eq_one (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    ∫ x, inverseFourierDensity ψ x = 1 := by
  -- Deduce from charFun_inverseFourierDensity at ξ = 0
  have h := charFun_inverseFourierDensity ψ hψc hpd h0 hI 0
  -- At ξ = 0, exp(0·x·I) = 1, so (r : ℝ) • 1 = ↑r
  have heq : ∀ x : ℝ, (inverseFourierDensity ψ x : ℝ) • exp ((0 : ℝ) * ↑x * I) =
      ↑(inverseFourierDensity ψ x) := by
    intro x; simp [Complex.real_smul]
  simp_rw [heq, h0] at h
  -- h : ∫ x, (↑(inverseFourierDensity ψ x) : ℂ) = 1
  have := congr_arg Complex.re h
  simp only [Complex.one_re] at this
  rwa [show (∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ)).re =
    ∫ x, inverseFourierDensity ψ x from by
    have : ∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ) =
      ↑(∫ x, inverseFourierDensity ψ x) := integral_ofReal
    rw [this, Complex.ofReal_re]] at this

/-- **Fourier inversion for PD L¹ functions.** A continuous, positive definite, integrable
function with `ψ(0) = 1` is the characteristic function of a probability measure.

Proof: The inverse Fourier density `ρ(x) = (1/2π) Re(∫ ψ(u) e^{-ixu} du)` is non-negative
(by the Fejér approximation argument), integrates to 1 (by Gaussian regularization), and
has characteristic function equal to `ψ` (by Fourier inversion). -/
private lemma exists_probMeasure_of_pd_integrable
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ)
    (h0 : ψ 0 = 1) (_hI : Integrable ψ volume) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, charFun (μ : Measure ℝ) ξ = ψ ξ := by
  -- Construct the measure with density ρ = inverseFourierDensity ψ
  set ρ := inverseFourierDensity ψ with hρ_def
  have hρ_nn : ∀ x, 0 ≤ ρ x := inverseFourierDensity_nonneg ψ hψc hpd _hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc _hI
  have hρ_int : ∫ x, ρ x = 1 := integral_inverseFourierDensity_eq_one ψ hψc hpd h0 _hI
  have hρ_integrable : Integrable ρ volume := integrable_of_integral_eq_one hρ_int
  -- Define the measure
  set μ_raw : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ_def
  -- Show it's a probability measure
  have hμ_prob : IsProbabilityMeasure μ_raw := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [show (∫⁻ x, ENNReal.ofReal (ρ x)) = ENNReal.ofReal (∫ x, ρ x) from by
      rw [ofReal_integral_eq_lintegral_ofReal hρ_integrable (ae_of_all _ hρ_nn)]]
    rw [hρ_int, ENNReal.ofReal_one]
  -- Wrap as ProbabilityMeasure
  set μ_pm : ProbabilityMeasure ℝ := ⟨μ_raw, hμ_prob⟩ with hμ_pm_def
  refine ⟨μ_pm, fun ξ => ?_⟩
  -- Show charFun μ_pm ξ = ψ ξ
  simp only [charFun_apply_real]
  change ∫ x, exp (↑ξ * ↑x * I) ∂μ_raw = ψ ξ
  -- Rewrite the integral against μ_raw = withDensity(ofReal ρ)
  rw [hμ_def, integral_withDensity_eq_integral_toReal_smul
    (hρ_cont.measurable.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  -- Goal: ∫ x, (ENNReal.ofReal (inverseFourierDensity ψ x)).toReal • exp(ξxI) = ψ ξ
  -- Simplify toReal ∘ ofReal using non-negativity
  have h_eq : ∀ x : ℝ, (ENNReal.ofReal (inverseFourierDensity ψ x)).toReal =
      inverseFourierDensity ψ x := fun x => ENNReal.toReal_ofReal (hρ_nn x)
  simp_rw [h_eq]
  exact charFun_inverseFourierDensity ψ hψc hpd h0 _hI ξ


end ProbabilityTheory

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
import all Analysis.Fourier.Bochner.Lemmas.InverseFourierDensity

/-!
# Gaussian smoothing stage in the Bochner proof

For `φ : ℝ → ℂ` and `gₙ(ξ) = charFun (N(0, 1/(n+1))) ξ`, this internal stage proves that
`φₙ = φ · gₙ` is continuous, positive definite, integrable, and normalized by `φₙ 0 = 1`.
It also proves `φₙ(ξ) → φ(ξ)` for every `ξ` and the tightness criterion used by the final
Prokhorov argument.

This file contains only package-internal proof support for
`Analysis.Fourier.Bochner.Theorem`; it has no public declarations.

## Internal proof declarations

- For continuous positive-definite $\varphi$ with $\varphi(0)=1$, the private
  `integrable_smoothed` proves that
  $\varphi_n(\xi)=\varphi(\xi)\,\operatorname{charFun}(N(0,(n+1)^{-1}),\xi)$
  remains continuous, positive-definite, normalized, and integrable.
- `tendsto_smoothed` proves $\varphi_n(\xi)\to\varphi(\xi)$ for each $\xi$;
  `isTight_of_charFun_pointwise_tendsto` provides the tightness step used by
  the Prokhorov argument.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

/-- A pointwise limit of characteristic functions which is continuous at zero
forms a tight family. This delegates to Mathlib's Lévy convergence development. -/
private lemma isTight_of_charFun_pointwise_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφc : Continuous φ)
    (hconv : ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ))) :
    IsTightMeasureSet (range (fun n => (μs n : Measure ℝ))) :=
  MeasureTheory.isTightMeasureSet_of_tendsto_charFun hφc.continuousAt hconv

/-! ### Gaussian smoothing infrastructure -/

section GaussianSmoothing

/-- The Gaussian variance parameter for the n-th smoothing: `1/(n+1)` as an `ℝ≥0`. -/
private noncomputable def gaussianVar (n : ℕ) : ℝ≥0 := ⟨1 / (↑n + 1), by positivity⟩

/-- The `N(0, 1/(n+1))` Gaussian as a `ProbabilityMeasure`. -/
private noncomputable def gaussianPM (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (gaussianVar n), inferInstance⟩

@[simp]
private lemma gaussianPM_val (n : ℕ) :
    (gaussianPM n : Measure ℝ) = gaussianReal 0 (gaussianVar n) := rfl

/-- The characteristic function of `N(0, 1/(n+1))` is positive definite. -/
private lemma pd_gaussianCharFun (n : ℕ) :
    IsPositiveDefinite (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  show IsPositiveDefinite (fun ξ => charFun (gaussianPM n : Measure ℝ) ξ)
  exact MeasureTheory.ProbabilityMeasure.isPositiveDefinite_charFun (gaussianPM n)

/-- The smoothed function `φ · charFun(N(0,1/(n+1)))` is positive definite. -/
private lemma pd_smoothed {φ : ℝ → ℂ} (hpd : IsPositiveDefinite φ) (n : ℕ) :
    IsPositiveDefinite (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hpd.mul (pd_gaussianCharFun n)

/-- The smoothed function at 0 equals 1. -/
private lemma smoothed_at_zero {φ : ℝ → ℂ} (h0 : φ 0 = 1) (n : ℕ) :
    φ 0 * charFun (gaussianReal 0 (gaussianVar n)) 0 = 1 := by
  simp [h0, charFun_zero]

/-- Continuity of the Gaussian characteristic function. -/
private lemma continuous_charFun_gaussianVar (n : ℕ) :
    Continuous (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  simp_rw [charFun_gaussianReal]
  fun_prop

/-- Continuity of the smoothed function. -/
private lemma continuous_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ) (n : ℕ) :
    Continuous (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hφc.mul (continuous_charFun_gaussianVar n)

/-- The Gaussian charfun `ξ ↦ charFun(N(0,v))(ξ)` is integrable for `v > 0`.

Proof: `‖charFun(N(0,v)) ξ‖ = exp(-v/2 · ξ²)`, which is integrable as a Gaussian.
The norm equality follows from `charFun_gaussianReal` and the fact that the mean-0
Gaussian charfun has purely real, negative exponent. -/
private lemma integrable_charFun_gaussianVar (n : ℕ) :
    Integrable (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  set v := gaussianVar n
  have hv_pos : (0 : ℝ) < (v : ℝ≥0) := by
    have hval : ((v : ℝ≥0) : ℝ) = 1 / (↑n + 1) := rfl
    rw [hval]; positivity
  -- The norm of charFun(N(0,v)) ξ equals exp(-(v/2)·ξ²)
  have hnorm_eq : ∀ ξ : ℝ, ‖charFun (gaussianReal 0 v) ξ‖ = Real.exp (-((v : ℝ) / 2 * ξ ^ 2)) := by
    intro ξ
    rw [charFun_gaussianReal, Complex.norm_exp]
    congr 1
    simp only [ofReal_zero, mul_zero, zero_mul, zero_sub,
      Complex.neg_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    rw [show ((↑ξ : ℂ) ^ 2).re = ξ ^ 2 by
      simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]]
    ring
  -- This function is integrable
  refine (integrable_exp_neg_mul_sq (by linarith : 0 < (v : ℝ) / 2)).mono'
    (continuous_charFun_gaussianVar n).aestronglyMeasurable ?_
  exact ae_of_all _ fun ξ => by
    rw [hnorm_eq]
    exact Real.exp_le_exp_of_le (by nlinarith)

/-- Integrability of the smoothed function (bounded by Gaussian). -/
private lemma integrable_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hpd : IsPositiveDefinite φ) (h0 : φ 0 = 1) (n : ℕ) :
    Integrable (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  exact (integrable_charFun_gaussianVar n).mono
    (continuous_smoothed hφc n).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [norm_mul]
      calc ‖φ ξ‖ * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖
          ≤ 1 * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ :=
            mul_le_mul_of_nonneg_right (hpd.norm_le_one h0 ξ) (norm_nonneg _)
        _ = ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ := one_mul _)

/-- The Gaussian charfun at a fixed `ξ` tends to 1 as the variance → 0. -/
private lemma tendsto_gaussianCharFun_one (ξ : ℝ) :
    Tendsto (fun n => charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 1) := by
  -- charFun(N(0,1/(n+1))) ξ → 1 as the Gaussian variance → 0
  simp_rw [charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, zero_sub]
  -- Goal: cexp(-(↑↑(gaussianVar n) * ↑ξ^2/2)) → 1
  rw [show (1 : ℂ) = cexp 0 from by simp]
  apply Filter.Tendsto.cexp
  -- The exponent -(v_n * ξ²/2) → 0 since v_n → 0
  rw [show (0 : ℂ) = -(0 * (↑ξ : ℂ) ^ 2 / 2) from by simp]
  -- Need: ↑↑(gaussianVar n) → 0 in ℂ
  have hv_tendsto : Tendsto (fun n : ℕ => (↑↑(gaussianVar n) : ℂ)) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
    exact (Complex.continuous_ofReal.tendsto 0).comp (by
      show Tendsto (fun n : ℕ => (↑(gaussianVar n) : ℝ)) atTop (𝓝 0)
      simp only [gaussianVar]
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
  exact (((hv_tendsto.mul tendsto_const_nhds).div_const _).neg)

/-- The smoothed charfun converges pointwise to φ. -/
private lemma tendsto_smoothed (φ : ℝ → ℂ) (ξ : ℝ) :
    Tendsto (fun n => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 (φ ξ)) := by
  conv_rhs => rw [show φ ξ = φ ξ * 1 from (mul_one _).symm]
  exact tendsto_const_nhds.mul (tendsto_gaussianCharFun_one ξ)

end GaussianSmoothing


end ProbabilityTheory

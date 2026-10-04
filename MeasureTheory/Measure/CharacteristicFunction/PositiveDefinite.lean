/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Analysis.Fourier.PositiveDefinite
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Positive Definiteness of Characteristic Functions

This file connects the pure positive-definite-function API to characteristic functions of
probability measures. The main identity expresses the characteristic-function quadratic form
as the integral of a squared modulus.
-/

open MeasureTheory Complex ComplexConjugate

namespace MeasureTheory.ProbabilityMeasure

/-- Pointwise, the quadratic kernel of a characteristic function is a squared modulus. -/
private theorem charFun_sum_integrand_eq_normSq
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) (a : ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * exp (↑(ξ i - ξ j) * ↑a * I) =
      ↑(Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I)))) := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (↑(ξ i - ξ j) : ℂ) * ↑a * I =
      ↑(ξ i) * ↑a * I + -(↑(ξ j) * ↑a * I) from by push_cast; ring, exp_add]
  simp only [map_mul, ← exp_conj, map_neg, conj_ofReal, conj_I, mul_neg, neg_neg]
  ring

private theorem integrable_charFun_term (μ : ProbabilityMeasure ℝ)
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) (i j : Fin n) :
    Integrable
      (fun a : ℝ => starRingEnd ℂ (c i) * c j * exp (↑(ξ i - ξ j) * ↑a * I))
      (μ : Measure ℝ) := by
  apply (integrable_const (‖starRingEnd ℂ (c i) * c j‖ : ℝ)).mono'
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · filter_upwards with a
    simp only [norm_mul,
      show (↑(ξ i - ξ j) : ℂ) * ↑a * I = ↑((ξ i - ξ j) * a) * I from by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one, le_refl]

private theorem integrable_charFun_sum_integrand (μ : ProbabilityMeasure ℝ)
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    Integrable
      (fun a : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * exp (↑(ξ i - ξ j) * ↑a * I))
      (μ : Measure ℝ) :=
  integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_charFun_term μ ξ c i j

/-- **Squared-modulus identity for a characteristic function.** With the convention
`charFun μ ξ = ∫ exp(i ξ x) dμ x`,

`∑ᵢ ∑ⱼ conj(cᵢ) cⱼ charFun μ (ξᵢ - ξⱼ)`
`= ∫ ‖∑ⱼ cⱼ exp(-i ξⱼ x)‖² dμ x`.

The identity uses no moment assumption. -/
theorem charFun_sum_eq_integral_normSq (μ : ProbabilityMeasure ℝ)
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun (μ : Measure ℝ) (ξ i - ξ j) =
      ∫ a : ℝ,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ)
        ∂(μ : Measure ℝ) := by
  simp only [charFun_apply_real]
  have hint : ∀ i j : Fin n, Integrable
      (fun a : ℝ => starRingEnd ℂ (c i) * c j * exp (↑(ξ i - ξ j) * ↑a * I))
      (μ : Measure ℝ) := integrable_charFun_term μ ξ c
  have h_pull : ∀ (r : ℂ) (f : ℝ → ℂ),
      r * ∫ a, f a ∂(μ : Measure ℝ) = ∫ a, r * f a ∂(μ : Measure ℝ) :=
    fun r f => (integral_const_mul r f).symm
  simp_rw [h_pull]
  simp_rw [(integral_finsetSum Finset.univ (fun j _ => hint _ j)).symm]
  rw [(integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))).symm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
    charFun_sum_integrand_eq_normSq ξ c a)

/-- The real part of the characteristic-function quadratic form is nonnegative. -/
theorem charFun_positiveSemiDefinite (μ : ProbabilityMeasure ℝ)
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun (μ : Measure ℝ) (ξ i - ξ j)).re := by
  have hform := charFun_sum_eq_integral_normSq μ ξ c
  have hint := integrable_charFun_sum_integrand μ ξ c
  have hnorm : Integrable
      (fun a : ℝ =>
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ))
      (μ : Measure ℝ) :=
    hint.congr (Filter.Eventually.of_forall fun a =>
      charFun_sum_integrand_eq_normSq ξ c a)
  rw [hform]
  have hre :
      (∫ a : ℝ,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ)
        ∂(μ : Measure ℝ)).re =
      ∫ a : ℝ,
        Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I)))
        ∂(μ : Measure ℝ) :=
    ((@RCLike.reCLM ℂ _).integral_comp_comm hnorm).symm
  rw [hre]
  exact integral_nonneg fun a => Complex.normSq_nonneg _

end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory.IsPositiveDefinite

/-- The characteristic function of a probability measure is positive definite. -/
theorem of_charFun (μ : ProbabilityMeasure ℝ) :
    IsPositiveDefinite (fun ξ => charFun (μ : Measure ℝ) ξ) := by
  intro n ξ c
  rw [Complex.nonneg_iff]
  constructor
  · exact MeasureTheory.ProbabilityMeasure.charFun_positiveSemiDefinite μ ξ c
  · have hform := MeasureTheory.ProbabilityMeasure.charFun_sum_eq_integral_normSq μ ξ c
    have hint := MeasureTheory.ProbabilityMeasure.integrable_charFun_sum_integrand μ ξ c
    have hnorm : Integrable
        (fun a : ℝ =>
          (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ))
        (μ : Measure ℝ) :=
      hint.congr (Filter.Eventually.of_forall fun a =>
        MeasureTheory.ProbabilityMeasure.charFun_sum_integrand_eq_normSq ξ c a)
    rw [hform]
    rw [show
      (∫ a : ℝ,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ)
        ∂(μ : Measure ℝ)).im =
      ∫ a : ℝ,
        ((Complex.normSq (∑ j : Fin n, c j * exp (-(↑(ξ j) * ↑a * I))) : ℂ).im)
        ∂(μ : Measure ℝ) from
      ((@RCLike.imCLM ℂ _).integral_comp_comm hnorm).symm]
    simp

end ProbabilityTheory.IsPositiveDefinite

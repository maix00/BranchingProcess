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
public import Mathlib.Analysis.InnerProductSpace.Basic
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
open scoped InnerProductSpace

namespace MeasureTheory.ProbabilityMeasure

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise, the quadratic kernel of a characteristic function is a squared modulus. -/
private theorem charFun_sum_integrand_eq_normSq
    {n : ℕ} (ξ : Fin n → E) (c : Fin n → ℂ) (a : E) :
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * exp (↑(⟪a, ξ i - ξ j⟫_ℝ) * I) =
      ↑(Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I)))) := by
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (↑(⟪a, ξ i - ξ j⟫_ℝ) : ℂ) * I =
      ↑(⟪a, ξ i⟫_ℝ) * I + -(↑(⟪a, ξ j⟫_ℝ) * I) from by
        rw [inner_sub_right]
        push_cast
        ring, exp_add]
  simp only [map_mul, ← exp_conj, map_neg, conj_ofReal, conj_I, mul_neg, neg_neg]
  ring

private theorem integrable_charFun_term (μ : ProbabilityMeasure E)
    {n : ℕ} (ξ : Fin n → E) (c : Fin n → ℂ) (i j : Fin n) :
    Integrable
      (fun a : E => starRingEnd ℂ (c i) * c j * exp (↑(⟪a, ξ i - ξ j⟫_ℝ) * I))
      (μ : Measure E) := by
  apply (integrable_const (‖starRingEnd ℂ (c i) * c j‖ : ℝ)).mono'
  · exact (by fun_prop : Continuous _).aestronglyMeasurable
  · filter_upwards with a
    simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one, le_refl]

private theorem integrable_charFun_sum_integrand (μ : ProbabilityMeasure E)
    {n : ℕ} (ξ : Fin n → E) (c : Fin n → ℂ) :
    Integrable
      (fun a : E => ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * exp (↑(⟪a, ξ i - ξ j⟫_ℝ) * I))
      (μ : Measure E) :=
  integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => integrable_charFun_term μ ξ c i j

/-- **Squared-modulus identity for a characteristic function.** With the convention
`charFun μ ξ = ∫ exp(i ⟪x, ξ⟫) dμ x`,

`∑ᵢ ∑ⱼ conj(cᵢ) cⱼ charFun μ (ξᵢ - ξⱼ)`
`= ∫ ‖∑ⱼ cⱼ exp(-i ⟪x, ξⱼ⟫)‖² dμ x`.

The identity uses no moment assumption. -/
theorem charFun_sum_eq_integral_normSq (μ : ProbabilityMeasure E)
    {n : ℕ} (ξ : Fin n → E) (c : Fin n → ℂ) :
    ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun (μ : Measure E) (ξ i - ξ j) =
      ∫ a : E,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I))) : ℂ)
        ∂(μ : Measure E) := by
  simp only [charFun_apply]
  have hint : ∀ i j : Fin n, Integrable
      (fun a : E => starRingEnd ℂ (c i) * c j * exp (↑(⟪a, ξ i - ξ j⟫_ℝ) * I))
      (μ : Measure E) := integrable_charFun_term μ ξ c
  have h_pull : ∀ (r : ℂ) (f : E → ℂ),
      r * ∫ a, f a ∂(μ : Measure E) = ∫ a, r * f a ∂(μ : Measure E) :=
    fun r f => (integral_const_mul r f).symm
  simp_rw [h_pull]
  simp_rw [(integral_finsetSum Finset.univ (fun j _ => hint _ j)).symm]
  rw [(integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))).symm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
    charFun_sum_integrand_eq_normSq ξ c a)

private theorem integrable_charFun_normSq (μ : ProbabilityMeasure E)
    {n : ℕ} (ξ : Fin n → E) (c : Fin n → ℂ) :
    Integrable
      (fun a : E =>
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I))) : ℂ))
      (μ : Measure E) := by
  have hint := integrable_charFun_sum_integrand μ ξ c
  exact hint.congr (Filter.Eventually.of_forall fun a =>
    charFun_sum_integrand_eq_normSq ξ c a)

/-- The characteristic function of a probability measure on a real inner product space is
positive definite. -/
theorem isPositiveDefinite_charFun (μ : ProbabilityMeasure E) :
    IsPositiveDefinite (fun ξ => charFun (μ : Measure E) ξ) := by
  intro n ξ c
  rw [Complex.nonneg_iff]
  constructor
  · rw [charFun_sum_eq_integral_normSq]
    have hnorm := integrable_charFun_normSq μ ξ c
    have hre :
        (∫ a : E,
          (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I))) : ℂ)
          ∂(μ : Measure E)).re =
        ∫ a : E,
          Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I)))
          ∂(μ : Measure E) :=
      ((@RCLike.reCLM ℂ _).integral_comp_comm hnorm).symm
    rw [hre]
    exact integral_nonneg fun a => Complex.normSq_nonneg _
  · rw [charFun_sum_eq_integral_normSq]
    have hnorm := integrable_charFun_normSq μ ξ c
    rw [show
      (∫ a : E,
        (Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I))) : ℂ)
        ∂(μ : Measure E)).im =
      ∫ a : E,
        ((Complex.normSq (∑ j : Fin n, c j * exp (-(↑(⟪a, ξ j⟫_ℝ) * I))) : ℂ).im)
        ∂(μ : Measure E) from
      ((@RCLike.imCLM ℂ _).integral_comp_comm hnorm).symm]
    simp

end InnerProductSpace

end MeasureTheory.ProbabilityMeasure

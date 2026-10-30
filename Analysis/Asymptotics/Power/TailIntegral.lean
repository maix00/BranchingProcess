/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Analysis.Asymptotics.RegularVariation.Integral.Basic

/-!
# Integrals of power-tailed functions

## Public declarations

* `Asymptotics.tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul`: if
  `t ^ β * g(t) → C > 0`, `g` is antitone, nonnegative, and bounded by one,
  and `β < 1`, then
  `U ^ (β - 1) * ∫₀ᵁ g(t) dt → C / (1 - β)`. This is the power-tail case of
  Theorem 1.5.11(i) in N. H. Bingham, C. M. Goldie, and J. L. Teugels,
  *Regular Variation*, Encyclopedia of Mathematics and its Applications 27,
  Cambridge University Press (1987), DOI `10.1017/CBO9780511721434`.

This file proves the integral form of Karamata's theorem for a nonnegative,
antitone function bounded by one. The assumptions are stated directly in terms
of a power-tail limit, without introducing a separate regular-variation
structure. It is a power-tail specialization of Theorem 1.5.11(i) in N. H.
Bingham, C. M. Goldie, and J. L. Teugels, *Regular Variation*, Encyclopedia
of Mathematics and its Applications 27, Cambridge University Press (1987),
DOI 10.1017/CBO9780511721434.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Interval

namespace Asymptotics

private lemma regularlyVarying_of_tendsto_rpow_mul
    {g : ℝ → ℝ} {β C : ℝ} (hC : 0 < C)
    (hlim : Tendsto (fun t : ℝ => t ^ β * g t) atTop (nhds C)) :
    IsRegularlyVaryingAtTop g (-β) := by
  have hslow : IsSlowlyVaryingAtTop (fun t : ℝ => t ^ β * g t) :=
    IsSlowlyVaryingAtTop.of_tendsto_pos hC hlim
  have hprod := (IsRegularlyVaryingAtTop.rpow (-β)).mul hslow
  have heq : (fun t : ℝ => t ^ (-β) * (t ^ β * g t)) =ᶠ[atTop] g := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hpow : t ^ (-β) * t ^ β = 1 := by
      rw [← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero]
    calc
      t ^ (-β) * (t ^ β * g t) = (t ^ (-β) * t ^ β) * g t := by ring
      _ = g t := by rw [hpow, one_mul]
  simpa only [add_zero] using hprod.congr heq

/-- A bounded antitone function with tail `g(t) ~ C t⁻ᵝ`, for `β < 1`, has
integral asymptotic `∫₀ᵁ g(t) dt ~ C U^(1-β) / (1-β)`. This is a power-tail
specialization of Theorem 1.5.11(i) in N. H. Bingham, C. M. Goldie, and J. L.
Teugels, *Regular Variation*, Encyclopedia of Mathematics and its
Applications 27, Cambridge University Press (1987), DOI
10.1017/CBO9780511721434. -/
theorem tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul
    {g : ℝ → ℝ} {β C : ℝ}
    (hβ₁ : β < 1) (hC : 0 < C)
    (hg_anti : Antitone g)
    (hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t)
    (hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1)
    (hlim : Tendsto (fun t : ℝ => t ^ β * g t) atTop (nhds C)) :
    Tendsto (fun U : ℝ => U ^ (β - 1) * ∫ t in (0:ℝ)..U, g t)
      atTop (nhds (C / (1 - β))) := by
  have hreg : IsRegularlyVaryingAtTop g (-β) :=
    regularlyVarying_of_tendsto_rpow_mul hC hlim
  have hβ₀ : 0 ≤ β := by
    have hratio := hreg.ratio_tendsto (c := 2) (by norm_num)
    have hratio_le : ∀ᶠ U : ℝ in atTop, g (2 * U) / g U ≤ 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hreg.eventually_pos]
        with U hU hgU
      apply (div_le_one hgU).2
      exact hg_anti (by nlinarith)
    have hlimit_le : (2 : ℝ) ^ (-β) ≤ 1 :=
      le_of_tendsto_of_tendsto hratio tendsto_const_nhds hratio_le
    by_contra hβ
    have hneg : 0 < -β := by linarith
    have hgt : 1 < (2 : ℝ) ^ (-β) :=
      Real.one_lt_rpow (by norm_num) hneg
    linarith
  have hKaramata := hreg.tendsto_intervalIntegral_div_mul_of_antitone
    hβ₀ (by linarith : β < 1) hg_anti hg_nonneg hg_le_one
  have hfactor : Tendsto (fun U : ℝ => U ^ β * g U) atTop (nhds C) := hlim
  have heq : (fun U : ℝ => U ^ (β - 1) * ∫ t in (0:ℝ)..U, g t) =ᶠ[atTop]
      fun U => (U ^ β * g U) *
        ((∫ t in (0:ℝ)..U, g t) / (U * g U)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hreg.eventually_pos]
      with U hU hgU
    have hpow : U ^ (β - 1) = U ^ β / U := by
      calc
        U ^ (β - 1) = U ^ β / U ^ (1 : ℝ) := Real.rpow_sub hU β 1
        _ = U ^ β / U := by rw [Real.rpow_one]
    rw [hpow]
    field_simp [ne_of_gt hU, ne_of_gt hgU]
  have hresult := hfactor.mul hKaramata
  have hresult' := hresult.congr' heq.symm
  simpa [div_eq_mul_inv, mul_assoc] using hresult'

end Asymptotics

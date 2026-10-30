/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.CharacteristicFunction.CosineDefect
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic
import Probability.Distributions.Stable.Gaussian.Basic

import Probability.Distributions.CharacteristicFunction.FirstOrder
import Probability.Distributions.CharacteristicFunction.TruncatedMoment
import Probability.Distributions.Stable.Attraction.Normal.Basic
import Probability.Distributions.Stable.Attraction.Normal.Centering
import Probability.Distributions.Stable.Attraction.Normal.QuadraticTail
import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Centering
import Probability.Distributions.Stable.Attraction.Norming.SpecialCases.IndexTwo

/-!
# Quadratic norming in the Gaussian domain of attraction

## Public declarations

- `IsInDomainOfAttractionAlong.tendsto_normalizedCosineDefect_of_gaussian`:
  $2x^2C_\nu(1/x)/L^*(x)\to1$.
- `IsInDomainOfAttractionAlong.tendsto_truncatedSecondMoment_div_scaledNormDefect_of_gaussian_of_integrable_centered`:
  for centered integrable $\nu$,
  $L^*(x)/(x^2D_\nu(1/x))\to1$, where
  $D_\nu(u)=1-|\widehat\nu(u)|^2$.
- `IsInDomainOfAttractionAlong.isStableNorming_two_of_integrable_centered`
  and `IsInDomainOfAttractionAlong.isStableNorming_two_of_gaussian` provide
  the quadratic stable-norming relation.
- `IsInDomainOfAttractionAlong.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian`:
  for $c>0$, $nL^*(ca_n)/a_n^2\to1$.
- `IsInDomainOfAttractionAlong.tendsto_nat_mul_twoSidedTail_mul_of_gaussian`:
  for $c>0$, $n\nu\{|x|>ca_n\}\to0$.

The normal-domain truncated-moment characterization used here is W. Feller,
*An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.
(Wiley, 1971), Section XVII.5, Theorem 2 (ISBN 978-0-471-25709-7); the
quadratic norming and characteristic-defect conclusions are derived from that
criterion and the local characteristic-function estimates.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- In the normal domain of attraction, the real-part characteristic defect
and the truncated second moment have their standard quadratic asymptotic.
This is the part of the exponent-two comparison that does not involve the
phase of the characteristic function. -/
theorem IsInDomainOfAttractionAlong.tendsto_normalizedCosineDefect_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto
      (fun x : ℝ => 2 * x ^ 2 * cosineDefectIntegral ν x⁻¹ /
        truncatedSecondMoment ν x) atTop (nhds 1) := by
  exact tendsto_normalizedCosineDefect_of_slowVariation_and_tail ν
    h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
    h.tendsto_secondTailRatio_of_gaussian

/-- In the normal domain, centering and a finite first moment make the phase
of the characteristic function negligible compared with the quadratic
cosine defect. Thus the truncated second moment is asymptotic to the squared-
modulus defect with the usual exponent-two normalization. No second moment is
assumed. -/
theorem IsInDomainOfAttractionAlong.tendsto_truncatedSecondMoment_div_scaledNormDefect_of_gaussian_of_integrable_centered
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0) :
    Tendsto
      (fun x : ℝ => truncatedSecondMoment ν x /
        (x ^ 2 * (1 - ‖charFun ν (x⁻¹)‖ ^ 2))) atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let D : ℝ → ℝ := fun x => 1 - ‖charFun ν (x⁻¹)‖ ^ 2
  let Q : ℝ → ℝ := fun x => cosineDefectIntegral ν (x⁻¹)
  have hcos : Tendsto (fun x : ℝ => 2 * x ^ 2 * Q x / V x)
      atTop (nhds 1) := by
    simpa [Q, V] using h.tendsto_normalizedCosineDefect_of_gaussian
  have hphase := tendsto_mul_charFun_sub_one_of_integrable_id_of_integral_eq_zero
    hint hmean
  have hphaseNormSq : Tendsto
      (fun x : ℝ => ‖(x : ℂ) * (charFun ν (x⁻¹) - 1)‖ ^ 2)
      atTop (nhds 0) := by
    simpa using (hphase.norm.pow 2)
  have hphaseSq : Tendsto
      (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2)
      atTop (nhds 0) := by
    apply hphaseNormSq.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    ring
  have hVpos := h.eventually_pos_truncatedSecondMoment_of_gaussian
  obtain ⟨R, hR⟩ := eventually_atTop.1 hVpos
  let R' : ℝ := max R 1
  have hR'pos : 0 < R' := by
    dsimp [R']
    positivity
  have hR'large : R ≤ R' := by
    dsimp [R']
    exact le_max_left _ _
  have hVbase : 0 < V R' := by
    exact hR R' hR'large
  have hVlower : ∀ᶠ x : ℝ in atTop, V R' ≤ V x := by
    filter_upwards [eventually_ge_atTop R'] with x hx
    exact truncatedSecondMoment_mono ν hR'pos.le hx
  have herror : Tendsto
      (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x)
      atTop (nhds 0) := by
    have hupper := hphaseSq.div_const (V R')
    have hupper' : Tendsto
        (fun x : ℝ => x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V R')
        atTop (nhds 0) := by
      simpa [hVbase.ne'] using hupper
    have hbounds : ∀ᶠ x : ℝ in atTop,
        0 ≤ x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x ∧
          x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x ≤
            x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V R' := by
      filter_upwards [hVlower, hVpos] with x hVx hVxpos
      constructor
      · exact div_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg _)) hVxpos.le
      · exact div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg x) (sq_nonneg _)) hVbase hVx
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper'
    · exact hbounds.mono fun x hx => hx.1
    · exact hbounds.mono fun x hx => hx.2
  have hscaled : Tendsto (fun x : ℝ => x ^ 2 * D x / V x)
      atTop (nhds 1) := by
    have hdecomp : (fun x : ℝ => x ^ 2 * D x / V x) =ᶠ[atTop]
        fun x => 2 * x ^ 2 * Q x / V x -
          x ^ 2 * ‖charFun ν (x⁻¹) - 1‖ ^ 2 / V x := by
      filter_upwards [] with x
      have hid := one_sub_norm_charFun_sq_eq_two_cosineDefect_sub_norm_sq ν (x⁻¹)
      dsimp [D, Q, V]
      rw [hid]
      ring
    have htemp := hcos.sub herror
    simpa using htemp.congr' hdecomp.symm
  have hDpos : ∀ᶠ x : ℝ in atTop, 0 < D x := by
    let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
      (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
    have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
    simpa [D] using tendsto_inv_atTop_nhdsGT_zero.eventually hpos
  have hscaledInv := hscaled.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvEq : (fun x : ℝ => (x ^ 2 * D x / V x)⁻¹) =ᶠ[atTop]
      fun x => V x / (x ^ 2 * D x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos, hDpos]
      with x hx hVx hDx
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
    have hDx' : D x ≠ 0 := hDx.ne'
    have hVx' : V x ≠ 0 := hVx.ne'
    field_simp [hx2, hDx', hVx']
  simpa [V] using hscaledInv.congr' hinvEq

/-- A centered integrable law in the standard Gaussian domain of attraction
has the exponent-two stable norming relation, including when its second
moment is infinite. -/
theorem IsInDomainOfAttractionAlong.isStableNorming_two_of_integrable_centered
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center)
    (hint : Integrable (fun x : ℝ => x) ν)
    (hmean : (∫ x : ℝ, x ∂ν) = 0)
    (hscalePos : ∀ n, 0 < n → 0 < scale n) :
    IsStableNorming 2 ν scale := by
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hscaleTop : Tendsto scale atTop atTop := h.tendsto_scale_atTop hlimit
  have hdefect : Tendsto
      (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))
      atTop (nhds 1) := h.gaussian_defect_data.2.2
  have hcompat :=
    h.tendsto_truncatedSecondMoment_div_scaledNormDefect_of_gaussian_of_integrable_centered
      hint hmean
  have hcompatSeq : Tendsto
      (fun n : ℕ => truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)))
      atTop (nhds 1) := hcompat.comp hscaleTop
  have hproduct := hcompatSeq.mul hdefect
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hdefectEq : (fun n : ℕ =>
      truncatedSecondMoment ν (scale n) /
        (scale n ^ 2 * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) *
        ((n : ℝ) * (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2))) =ᶠ[atTop]
      fun n => (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 := by
    filter_upwards [h.eventually_scale_pos, hnatPos,
      hdefect.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hsn hnn hdn
    have hsn' : scale n ≠ 0 := ne_of_gt hsn
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hnn
    have hd : 1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2 ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hdn
      norm_num at hdn
    field_simp [hsn', hnn', hd]
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) * truncatedSecondMoment ν (scale n) /
        scale n ^ 2) atTop (nhds 1) := by
    simpa using hproduct.congr' hdefectEq
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2 > 0 :=
    hratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hmomentPos : ∀ᶠ n : ℕ in atTop,
      0 < truncatedSecondMoment ν (scale n) := by
    filter_upwards [hratioPos, hnatPos, h.eventually_scale_pos]
      with n hq hn hsn
    have hnum : 0 < (n : ℝ) * truncatedSecondMoment ν (scale n) :=
      (div_pos_iff_of_pos_right (sq_pos_of_pos hsn)).mp hq
    exact (mul_pos_iff_of_pos_left hn).mp hnum
  have hinv := hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hinvEq : (fun n : ℕ =>
      ((n : ℝ) * truncatedSecondMoment ν (scale n) / scale n ^ 2)⁻¹) =ᶠ[atTop]
      fun n => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ) := by
    filter_upwards [hmomentPos, hnatPos, h.eventually_scale_pos] with n hmoment hn hsn
    have hpow : scale n ^ (2 : ℝ) = scale n ^ (2 : ℕ) :=
      Real.rpow_natCast (scale n) 2
    rw [hpow]
    have hnn' : (n : ℝ) ≠ 0 := ne_of_gt hn
    field_simp [hmoment.ne', hnn']
  have hnormRatio : Tendsto
      (fun n : ℕ => scale n ^ (2 : ℝ) /
        truncatedSecondMoment ν (scale n) / (n : ℝ))
      atTop (nhds 1) := by
    simpa using hinv.congr' hinvEq
  refine ⟨hscalePos, hscaleTop, ?_⟩
  simpa only [stableSlowVariation_two] using hnormRatio

/-- An uncentered Gaussian-domain normalization is the quadratic stable
norming, including in the infinite-variance case. The attraction hypothesis
implies first-moment integrability and zero mean; only positivity at the
finitely many initial indices is stated explicitly. -/
theorem IsInDomainOfAttractionAlong.isStableNorming_two_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n) :
    IsStableNorming 2 ν scale := by
  exact h.isStableNorming_two_of_integrable_centered
    h.integrable_id_of_gaussian h.integral_eq_zero_of_gaussian hscalePos

/-- Along a centered Gaussian-domain norming sequence, every fixed positive
multiple of the cutoff has the same normalized truncated-variance profile.
This is the triangular-array variance input for the exponent-two path limit. -/
theorem IsInDomainOfAttractionAlong.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      truncatedSecondMoment ν (c * scale n) / scale n ^ 2)
      atTop (nhds 1) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hnorm : IsStableNorming 2 ν scale :=
    h.isStableNorming_two_of_gaussian hscalePos
  have hbase := hnorm.tendsto_nat_mul_truncatedSecondMoment_div_sq
  have hratio := h.truncatedSecondMoment_isSlowlyVarying_of_gaussian.ratio_tendsto hc
  have hratioSeq := hratio.comp hnorm.2.1
  have hbasePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hnorm.2.1.eventually (eventually_gt_atTop 0)
  have hVpos : ∀ᶠ n : ℕ in atTop, 0 < V (scale n) :=
    hnorm.2.1.eventually h.eventually_pos_truncatedSecondMoment_of_gaussian
  have heq : (fun n : ℕ =>
      ((n : ℝ) * V (scale n) / scale n ^ 2) *
        (V (c * scale n) / V (scale n))) =ᶠ[atTop]
      fun n => (n : ℝ) * V (c * scale n) / scale n ^ 2 := by
    filter_upwards [hbasePos, hVpos] with n hb hV
    field_simp [ne_of_gt hb, ne_of_gt hV]
  have hresult := hbase.mul hratioSeq
  simpa [Real.rpow_zero, V] using hresult.congr' heq

/-- Under centered Gaussian attraction, the expected number of increments
larger than any fixed multiple of the norming scale tends to zero. This is the
quadratic-tail ratio limit that removes macroscopic jumps in the exponent-two path
limit, including for infinite-variance laws. -/
theorem IsInDomainOfAttractionAlong.tendsto_nat_mul_twoSidedTail_mul_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0))
    (hscalePos : ∀ n, 0 < n → 0 < scale n)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) * ν.real
      {x : ℝ | c * scale n < |x|}) atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let F : ℝ → ℝ := fun x => x ^ 2 * tail x / V x
  have hnorm : IsStableNorming 2 ν scale :=
    h.isStableNorming_two_of_gaussian hscalePos
  have hprofile := h.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq_of_gaussian
    hscalePos c hc
  have hscaleTop : Tendsto scale atTop atTop := hnorm.2.1
  have hscaledTop : Tendsto (fun n : ℕ => c * scale n) atTop atTop :=
    (tendsto_id.const_mul_atTop hc).comp hscaleTop
  have hF := h.tendsto_secondTailRatio_of_gaussian
  have hFseq := hF.comp hscaledTop
  have hFdiv : Tendsto (fun n : ℕ => F (c * scale n) / c ^ 2)
      atTop (nhds 0) := by
    simpa [F, tail] using hFseq.div_const (c ^ 2)
  have hVpos : ∀ᶠ n : ℕ in atTop, 0 < V (c * scale n) :=
    hscaledTop.eventually h.eventually_pos_truncatedSecondMoment_of_gaussian
  have hscalePosSeq : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have heq : (fun n : ℕ =>
      ((n : ℝ) * V (c * scale n) / scale n ^ 2) *
        (F (c * scale n) / c ^ 2)) =ᶠ[atTop]
      fun n => (n : ℝ) * tail (c * scale n) := by
    filter_upwards [hVpos, hscalePosSeq] with n hV hb
    dsimp [F, tail, V]
    field_simp [ne_of_gt hc, ne_of_gt hV, ne_of_gt hb]
    calc
      _ = (n : ℝ) * ν.real {x : ℝ | c * scale n < |x|} *
          (truncatedSecondMoment ν (c * scale n) *
            (truncatedSecondMoment ν (c * scale n))⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hV), mul_one]
  have hresult := hprofile.mul hFdiv
  simpa only [mul_zero, zero_mul] using hresult.congr' heq
end ProbabilityTheory

end

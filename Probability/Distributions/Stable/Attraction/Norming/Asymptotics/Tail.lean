/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Inverse
public import Probability.Distributions.Moments.Truncated.Layercake

import Probability.Distributions.Moments.Truncated.TailAsymptotics

/-!
# Tail and truncated-moment scales along stable normings

Regular variation of the two-sided tail and the stable norming relation give
explicit tail and truncated-second-moment limits at the norming scale.  These
are the distributional inputs for stable-domain local block estimates.

Let `T_ν(u)=ν({x : u<|x|})` and `V_ν(u)=∫_{|x|≤u}x²ν(dx)`. If the tail is
regularly varying with index `-α`, `0<α<2`, and `B` is a stable norming, then
for every fixed `c>0`,

\[
nT_ν(cB_n)\longrightarrow\frac{2-α}{α}c^{-α},\qquad
\frac{nV_ν(cB_n)}{B_n^2}\longrightarrow c^{2-α}.
\]

The same tail hypotheses give the truncated-moment factor limit

\[
L^*_ν(u)=u^{α-2}V_ν(u)\longrightarrow\frac{αC}{2-α}
\quad\text{if}\quad u^αT_ν(u)\longrightarrow C>0.
\]

## Public declarations

- For a stable norming `Bₙ` and a regularly varying two-sided tail of index `-α`, `n ν(|x| > Bₙ) → (2-α)/α`.
- For each fixed `c > 0`, `n ν(|x| > c Bₙ) → ((2-α)/α)c^(-α)`.
- At the same scale, `n Vν(c Bₙ) / Bₙ² → c^(2-α)`, where `Vν(u) = ∫_{|x| ≤ u} x² ν(dx)`.
- A regularly varying two-sided tail with `0 < α < 2` implies that `L*ν` is slowly varying.
- `tendsto_stableSlowVariation_of_layercake_and_tail`: if the normalized
  layer-cake tail and tail probability tend to `A` and `B`, then `L*ν → A-B`.
- `tendsto_stableSlowVariation_of_twoSidedTail`: if `0 < α < 2` and
  `u^α ν(|x|>u) → B>0`, then `L*ν → αB/(2-α)`.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- A finite layer-cake limit and two-sided tail limit determine the
stable-domain factor `L*` from the truncated moment. -/
theorem tendsto_stableSlowVariation_of_layercake_and_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral ν u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop (nhds (A - B)) := by
  change Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment ν u)
    atTop (nhds (A - B))
  exact tendsto_truncatedSecondMoment_scale_of_layercake_and_tail ν hA hB

/-- A two-sided power-tail asymptotic determines the stable-domain factor
`L*` from the truncated moment. If `u^α μ(|x| > u) → B` with `0 < α < 2`,
then `u^(α-2) ∫_{|x|≤u} x² ν(dx) → α B / (2-α)`. -/
theorem tendsto_stableSlowVariation_of_twoSidedTail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α B : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop
      (nhds (α * B / (2 - α))) := by
  change Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment ν u) atTop _
  exact tendsto_truncatedSecondMoment_scale_of_twoSidedTail ν hα₀ hα₂ hB hTail

/-- A regularly varying two-sided tail of index `-α`, for `0 < α < 2`, makes
the increment law's truncated-moment factor `L*` slowly varying. The
truncated-moment-to-tail ratio is obtained from the general Karamata theorem in
`Probability.Distributions.Moments.Truncated`. -/
theorem stableSlowVariation_isSlowlyVarying_of_regularlyVaryingTail
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hTail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν) := by
  let T : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let R : ℝ → ℝ := fun u =>
    truncatedSecondMoment ν u / (u ^ 2 * T u)
  have hTailFactor : Asymptotics.IsSlowlyVaryingAtTop
      (fun u : ℝ => u ^ α * T u) := by
    simpa [Asymptotics.IsSlowlyVaryingAtTop, T, mul_comm] using
      hTail.mul (Asymptotics.IsRegularlyVaryingAtTop.rpow α)
  have hratio : Tendsto R atTop
      (nhds (α / (2 - α))) := by
    simpa [R, T] using
      tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
        ν hα₀ hα₂ hTail
  have hconst : 0 < α / (2 - α) := div_pos hα₀ (by linarith)
  have hratioSlow : Asymptotics.IsSlowlyVaryingAtTop R :=
    Asymptotics.IsSlowlyVaryingAtTop.of_tendsto_pos hconst hratio
  have hfactorEq : (stableSlowVariation α ν) =ᶠ[atTop]
      fun u => (u ^ α * T u) * R u := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hTail.eventually_pos] with u hu hTu
    have hpow : u ^ (α - 2) = u ^ α / u ^ 2 := by
      calc
        u ^ (α - 2) = u ^ α / u ^ (2:ℝ) := Real.rpow_sub hu α 2
        _ = u ^ α / u ^ 2 := congrArg (fun z : ℝ => u ^ α / z)
          (Real.rpow_natCast u 2)
    have hden : u ^ 2 * T u ≠ 0 := ne_of_gt (mul_pos (sq_pos_of_pos hu) hTu)
    change u ^ (α - 2) * truncatedSecondMoment ν u = _
    rw [hpow]
    dsimp [R]
    field_simp [hden]
    rw [mul_div_assoc]
    rw [div_self (ne_of_gt hTu)]
    ring
  have hprodSlow := hTailFactor.mul hratioSlow
  refine ⟨?_, ?_⟩
  · filter_upwards [hfactorEq, hprodSlow.eventually_pos] with u hEq hpos
    rw [hEq]
    exact hpos
  · intro c hc
    have hcTop : Tendsto (fun u : ℝ => c * u) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hfactorScaled : (fun u : ℝ =>
        stableSlowVariation α ν (c * u) / stableSlowVariation α ν u) =ᶠ[atTop]
        fun u => (((c * u) ^ α * T (c * u)) * R (c * u)) /
          ((u ^ α * T u) * R u) := by
      filter_upwards [hfactorEq, hcTop.eventually hfactorEq] with u hEq hEqc
      rw [hEqc, hEq]
    exact (hprodSlow.ratio_tendsto hc).congr' hfactorScaled.symm

/-- Along a stable norming sequence, a regularly varying two-sided tail has
the normalized limit `(2 - α) / α`. -/
theorem IsStableNorming.tendsto_nat_mul_twoSidedTail_of_regularlyVarying
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ν.real {x : ℝ | normalization n < |x|}) atTop
      (nhds ((2 - α) / α)) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let moment : ℝ → ℝ := truncatedSecondMoment ν
  have hscaleTop : Tendsto normalization atTop atTop := hnorm.2.1
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < normalization n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have htailPos : ∀ᶠ n : ℕ in atTop, 0 < tail (normalization n) :=
    hscaleTop.eventually htail.eventually_pos
  have hratio : Tendsto (fun u : ℝ =>
      moment u / (u ^ 2 * tail u)) atTop
      (nhds (α / (2 - α))) := by
    simpa [moment, tail] using
      tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
        ν hα₀ hα₂ htail
  have hratioSeq := hratio.comp hscaleTop
  have hratioPos : ∀ᶠ n : ℕ in atTop,
      0 < moment (normalization n) ∧
        0 < normalization n ^ 2 * tail (normalization n) := by
    have hlimitPos : 0 < α / (2 - α) :=
      div_pos hα₀ (by linarith)
    have hratioEventuallyPos := hratioSeq.eventually (Ioi_mem_nhds hlimitPos)
    filter_upwards [hscalePos, htailPos, hratioEventuallyPos]
      with n hscale htailn hratioN
    have hden : 0 < normalization n ^ 2 * tail (normalization n) :=
      mul_pos (sq_pos_of_pos hscale) htailn
    have hmoment : 0 < moment (normalization n) := by
      have hprod := mul_pos hratioN hden
      have heq : moment (normalization n) /
          (normalization n ^ 2 * tail (normalization n)) *
          (normalization n ^ 2 * tail (normalization n)) =
          moment (normalization n) := by
        field_simp [ne_of_gt hden]
      change 0 < (moment (normalization n) /
        (normalization n ^ 2 * tail (normalization n))) *
        (normalization n ^ 2 * tail (normalization n)) at hprod
      rwa [heq] at hprod
    exact ⟨hmoment, hden⟩
  have hnormRatio : Tendsto (fun n : ℕ =>
      stableScaleTime α ν (normalization n) / (n : ℝ)) atTop
      (nhds 1) := by
    simpa only [stableScaleTime] using hnorm.2.2
  have hnormMoment : Tendsto (fun n : ℕ =>
      (normalization n ^ 2 / moment (normalization n)) / (n : ℝ))
      atTop (nhds 1) := by
    apply hnormRatio.congr'
    filter_upwards [hscalePos, hratioPos] with n hscale hpositive
    rw [stableScaleTime_eq_square_div_truncatedSecondMoment hscale hpositive.1]
  have hnormMomentInv := hnormMoment.inv₀ one_ne_zero
  have hnormMomentReciprocal : Tendsto (fun n : ℕ =>
      (n : ℝ) * moment (normalization n) / normalization n ^ 2)
      atTop (nhds 1) := by
    have heq : (fun n : ℕ =>
        (normalization n ^ 2 / moment (normalization n) / (n : ℝ))⁻¹) =ᶠ[atTop]
        fun n => (n : ℝ) * moment (normalization n) / normalization n ^ 2 := by
      filter_upwards [hscalePos, hratioPos,
        (eventually_gt_atTop (0 : ℕ)).mono fun n hn =>
          show (0 : ℝ) < (n : ℝ) from by exact_mod_cast hn]
        with n hscale hpositive hn
      have hn' : (n : ℝ) ≠ 0 := ne_of_gt hn
      field_simp [ne_of_gt (sq_pos_of_pos hscale), hpositive.1.ne', hn']
    simpa using hnormMomentInv.congr' heq
  have htailRatio : Tendsto (fun n : ℕ =>
      moment (normalization n) /
        (normalization n ^ 2 * tail (normalization n))) atTop
      (nhds (α / (2 - α))) := hratioSeq
  have hquotient := hnormMomentReciprocal.div htailRatio
    (ne_of_gt (div_pos hα₀ (by linarith)))
  have hquotientEq : (fun n : ℕ =>
      ((n : ℝ) * moment (normalization n) / normalization n ^ 2) /
        (moment (normalization n) /
          (normalization n ^ 2 * tail (normalization n)))) =ᶠ[atTop]
      fun n => (n : ℝ) * tail (normalization n) := by
    filter_upwards [hscalePos, hratioPos] with n hscale hpositive
    field_simp [ne_of_gt hpositive.1, ne_of_gt hpositive.2,
      ne_of_gt (sq_pos_of_pos hscale)]
  have hconst : 1 / (α / (2 - α)) = (2 - α) / α := by
    field_simp [ne_of_gt hα₀, ne_of_gt (show 0 < (2 : ℝ) - α by linarith)]
  rw [hconst] at hquotient
  exact hquotient.congr' hquotientEq

/-- The tail limit at a positive multiple of the norming scale, obtained from
the base-scale limit and regular variation. -/
theorem IsStableNorming.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
    {α c : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ν.real {x : ℝ | c * normalization n < |x|}) atTop
      (nhds (((2 - α) / α) * c ^ (-α))) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  have hbase := hnorm.tendsto_nat_mul_twoSidedTail_of_regularlyVarying
    hα₀ hα₂ htail
  have hratio := (htail.ratio_tendsto (c := c) hc).comp hnorm.2.1
  have htailPos := hnorm.2.1.eventually htail.eventually_pos
  have heq : (fun n : ℕ => (n : ℝ) * tail (normalization n) *
      (tail (c * normalization n) / tail (normalization n))) =ᶠ[atTop]
      fun n => (n : ℝ) * tail (c * normalization n) := by
    filter_upwards [htailPos] with n hn
    simp only [div_eq_mul_inv]
    calc
      (n : ℝ) * tail (normalization n) *
          (tail (c * normalization n) * (tail (normalization n))⁻¹) =
        (n : ℝ) * tail (c * normalization n) *
          (tail (normalization n) * (tail (normalization n))⁻¹) := by ring
      _ = (n : ℝ) * tail (c * normalization n) := by
        rw [mul_inv_cancel₀ (ne_of_gt hn), mul_one]
  have hprod := hbase.mul hratio
  have hprod' := hprod.congr' heq
  simpa [tail] using hprod'

/-- At any fixed positive multiple of a stable norming scale, the truncated
second moment has the corresponding normalized limit `c^(2 - α)`. -/
theorem IsStableNorming.tendsto_nat_mul_truncatedSecondMoment_mul_div_sq
    {α c : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α))
    (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      truncatedSecondMoment ν (c * normalization n) / normalization n ^ 2)
      atTop (nhds (c ^ (2 - α))) := by
  let tail : ℝ → ℝ := fun u => ν.real {x : ℝ | u < |x|}
  let moment : ℝ → ℝ := truncatedSecondMoment ν
  have htailScaled :=
    hnorm.tendsto_nat_mul_twoSidedTail_mul_of_regularlyVarying
      hα₀ hα₂ htail hc
  have hscaleTop : Tendsto normalization atTop atTop := hnorm.2.1
  have hscaledTop : Tendsto (fun n : ℕ => c * normalization n) atTop atTop :=
    (tendsto_id.const_mul_atTop hc).comp hscaleTop
  have hmomentRatio : Tendsto (fun u : ℝ =>
      moment u / (u ^ 2 * tail u)) atTop
      (nhds (α / (2 - α))) := by
    simpa [moment, tail] using
      tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
        ν hα₀ hα₂ htail
  have hmomentRatioScaled := hmomentRatio.comp hscaledTop
  have htailScaledPos : ∀ᶠ n : ℕ in atTop,
      0 < tail (c * normalization n) :=
    hscaledTop.eventually htail.eventually_pos
  have hproduct := htailScaled.mul hmomentRatioScaled
  have hconst₁ : (((2 - α) / α) * c ^ (-α)) * (α / (2 - α)) = c ^ (-α) := by
    field_simp [ne_of_gt hα₀,
      ne_of_gt (show 0 < (2 : ℝ) - α by linarith)]
  rw [hconst₁] at hproduct
  have hproductConst := hproduct.mul_const (c ^ 2)
  have hconst₂ : c ^ (-α) * c ^ 2 = c ^ (2 - α) := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_add hc]
    congr 1
    ring
  rw [hconst₂] at hproductConst
  have heq : (fun n : ℕ =>
      ((n : ℝ) * tail (c * normalization n)) *
        (moment (c * normalization n) /
          ((c * normalization n) ^ 2 * tail (c * normalization n))) * c ^ 2) =ᶠ[atTop]
      fun n => (n : ℝ) * moment (c * normalization n) / normalization n ^ 2 := by
    filter_upwards [hnorm.2.1.eventually (eventually_gt_atTop 0), htailScaledPos]
      with n hscale htailn
    field_simp [ne_of_gt hc, ne_of_gt hscale, ne_of_gt htailn]
  have hresult := hproductConst.congr' heq
  simpa [moment, tail] using hresult

end ProbabilityTheory

end

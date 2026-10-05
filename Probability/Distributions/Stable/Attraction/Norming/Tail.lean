/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Truncated
public import Probability.Distributions.Stable.Attraction.Norming.Inverse

/-!
# Tail and truncated-moment scales along stable normings

Regular variation of the two-sided tail and the stable norming relation give
explicit tail and truncated-second-moment limits at the norming scale.  These
are the distributional inputs for stable-domain local block estimates.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory

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

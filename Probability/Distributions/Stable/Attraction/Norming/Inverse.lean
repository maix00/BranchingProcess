/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming
public import Analysis.Asymptotics.BlockScale
public import Analysis.Asymptotics.RegularVariation.AsymptoticInverse

/-!
# Stable norming and its asymptotic inverse

This file converts the stable time scale into a spatial normalization along
rounded block lengths. It uses regular variation of the truncated second
moment and does not assume monotonicity of the stable time scale itself.
-/

open Filter MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- The truncated second moment has index `2 - α` when its normalized
truncated-moment factor is slowly varying. -/
theorem truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation
    {α : ℝ} {ν : Measure ℝ}
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Asymptotics.IsRegularlyVaryingAtTop
      (truncatedSecondMoment ν) (2 - α) := by
  have hproduct :=
    (Asymptotics.IsRegularlyVaryingAtTop.rpow (2 - α)).mul hslow
  have hEq : (fun u : ℝ => u ^ (2 - α) * stableSlowVariation α ν u) =ᶠ[atTop]
      truncatedSecondMoment ν := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    change u ^ (2 - α) * (u ^ (α - 2) * truncatedSecondMoment ν u) = _
    have hpow : u ^ (2 - α) * u ^ (α - 2) = 1 := by
      calc
        u ^ (2 - α) * u ^ (α - 2) = u ^ ((2 - α) + (α - 2)) :=
          (Real.rpow_add hu _ _).symm
        _ = u ^ (0 : ℝ) := by congr 1; ring
        _ = 1 := Real.rpow_zero u
    rw [← mul_assoc, hpow, one_mul]
  simpa using hproduct.congr hEq

/-- The truncated second moment is eventually nondecreasing. -/
theorem truncatedSecondMoment_isEventuallyMonotone (ν : Measure ℝ)
    [IsFiniteMeasure ν] :
    Asymptotics.IsEventuallyMonotoneAtTop (truncatedSecondMoment ν) := by
  refine ⟨0, ?_⟩
  intro u v hu huv
  exact truncatedSecondMoment_mono ν hu huv

/-- At every positive cutoff with positive truncated second moment, the stable
time scale is the square of the cutoff divided by that moment. -/
theorem stableScaleTime_eq_square_div_truncatedSecondMoment
    {α : ℝ} {ν : Measure ℝ} {u : ℝ}
    (hu : 0 < u) (hV : 0 < truncatedSecondMoment ν u) :
    stableScaleTime α ν u = u ^ 2 / truncatedSecondMoment ν u := by
  have hpow : u ^ (α - 2) = u ^ α / u ^ 2 := by
    calc
      u ^ (α - 2) = u ^ α / u ^ (2 : ℝ) := Real.rpow_sub hu α 2
      _ = u ^ α / u ^ 2 := congrArg (fun z : ℝ => u ^ α / z)
        (Real.rpow_natCast u 2)
  rw [stableScaleTime, stableSlowVariation, hpow]
  field_simp [ne_of_gt hV, ne_of_gt (sq_pos_of_pos hu)]

/-- If `0 < α < 2` and `L*` is slowly varying, then the stable time scale
diverges. The proof uses Potter's bound for the monotone truncated second
moment; it does not assume that `u ^ 2 / V(u)` is monotone. -/
theorem stableScaleTime_tendsto_atTop_of_stableSlowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Tendsto (stableScaleTime α ν) atTop atTop := by
  let β : ℝ := 2 - α
  let γ : ℝ := α / 2
  let p : ℝ := β + γ
  let C : ℝ := 2 ^ p
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ₂ : β < 2 := by dsimp [β]; linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V β := by
    simpa [V, β] using
      truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono hβ hγ
  obtain ⟨Rpositive, hRpositive⟩ := eventually_atTop.1 hVreg.eventually_pos
  let R : ℝ := max Rpotter Rpositive
  have hR : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le hRpotter (le_max_left _ _)
  have hRbase : 0 < V R := by
    change 0 < truncatedSecondMoment ν R
    exact hRpositive R (le_max_right _ _)
  have hp : 0 < p := by dsimp [p, β, γ]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  let K : ℝ := stableScaleTime α ν R / C
  have hK : 0 < K := by
    dsimp [K]
    have hκ : 0 < stableScaleTime α ν R := by
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hR hRbase]
      positivity
    exact div_pos hκ hC
  have hratioTop : Tendsto (fun u : ℝ => u / R) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_id.const_mul_atTop (inv_pos.mpr hR))
  have hlowerTop : Tendsto (fun u : ℝ => K * (u / R) ^ γ) atTop atTop := by
    exact ((tendsto_rpow_atTop hγ).comp hratioTop).const_mul_atTop hK
  have hlowerBound : ∀ᶠ u : ℝ in atTop,
      K * (u / R) ^ γ ≤ stableScaleTime α ν u := by
    filter_upwards [eventually_ge_atTop R] with u huR
    have hu : 0 < u := lt_of_lt_of_le hR huR
    have hVu : 0 < V u := by
      change 0 < truncatedSecondMoment ν u
      exact hRpositive u (le_trans (le_max_right _ _) huR)
    let q : ℝ := u / R
    have hqpos : 0 < q := by dsimp [q]; exact div_pos hu hR
    have hqge : 1 ≤ q := by
      dsimp [q]
      exact (one_le_div₀ hR).2 huR
    have hpot : V u / V R ≤ C * q ^ p := by
      simpa [C, p, q, V] using hpotter (le_max_left _ _) huR
    have hκRatio : stableScaleTime α ν u / stableScaleTime α ν R =
        q ^ 2 / (V u / V R) := by
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hu hVu,
        stableScaleTime_eq_square_div_truncatedSecondMoment hR hRbase]
      dsimp [q]
      dsimp [V] at hVu hRbase
      dsimp [V]
      field_simp [ne_of_gt hVu, ne_of_gt hRbase, ne_of_gt hR]
    have hratioLower : q ^ γ / C ≤ q ^ 2 / (V u / V R) := by
      apply (le_div_iff₀ (div_pos hVu hRbase)).2
      calc
        q ^ γ / C * (V u / V R) ≤ q ^ γ / C * (C * q ^ p) :=
          mul_le_mul_of_nonneg_left hpot (by positivity)
        _ = q ^ (γ + p) := by
          rw [div_mul_eq_mul_div]
          dsimp [C]
          field_simp
          exact (Real.rpow_add hqpos γ p).symm
        _ = q ^ 2 := by
          rw [show γ + p = 2 by dsimp [β, γ, p]; ring]
          exact Real.rpow_natCast q 2
    have hκR : 0 < stableScaleTime α ν R := by
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hR hRbase]
      positivity
    have hratioLower' :
        stableScaleTime α ν R * (q ^ γ / C) ≤ stableScaleTime α ν u := by
      calc
        stableScaleTime α ν R * (q ^ γ / C) ≤
            stableScaleTime α ν R * (q ^ 2 / (V u / V R)) :=
          mul_le_mul_of_nonneg_left hratioLower hκR.le
        _ = stableScaleTime α ν u := by
          rw [← hκRatio]
          field_simp [ne_of_gt hκR]
    have hKq : K * q ^ γ ≤ stableScaleTime α ν u := by
      dsimp [K]
      calc
        stableScaleTime α ν R / C * q ^ γ =
            stableScaleTime α ν R * (q ^ γ / C) := by ring
        _ ≤ stableScaleTime α ν u := hratioLower'
    simpa [q] using hKq
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hlowerTop.eventually (eventually_ge_atTop b), hlowerBound]
    with u hlarge hbound
  exact le_trans hlarge hbound

/-- For a stable norming sequence `B`, a block of length
`⌊c κ(aₙ)⌋₊` has spatial normalization asymptotic to `c^(1/α) aₙ`.
The inverse argument uses the monotone regularly varying truncated second
moment, rather than assuming monotonicity of `κ`. -/
theorem IsStableNorming.tendsto_floorBlock_normalization_div_scale
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hnorm : IsStableNorming α ν normalization)
    (hscale : Tendsto scale atTop atTop) (hconstant : 0 < constant) :
    Tendsto
      (fun n => normalization
        (Asymptotics.floorBlockLength
          (fun n => constant * stableScaleTime α ν (scale n)) n) / scale n)
      atTop (nhds (constant ^ (1 / α))) := by
  let block : ℕ → ℕ := Asymptotics.floorBlockLength
    (fun n => constant * stableScaleTime α ν (scale n))
  let κ : ℝ → ℝ := stableScaleTime α ν
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let β : ℝ := 2 - α
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ₂ : β < 2 := by dsimp [β]; linarith
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V β := by
    simpa [V, β] using
      truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  have hκtop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
    hα₀ hα₂ hslow
  have hargTop : Tendsto (fun n : ℕ => constant * κ (scale n)) atTop atTop := by
    exact (hκtop.comp hscale).const_mul_atTop hconstant
  have hblockTop : Tendsto block atTop atTop := by
    simpa [block] using Asymptotics.tendsto_floorBlockLength_atTop hargTop
  have hfloor : Tendsto
      (fun n => (block n : ℝ) / (constant * κ (scale n))) atTop (nhds 1) := by
    simpa [block] using Asymptotics.tendsto_floorBlockLength_div_argument hargTop
  have hκScalePos : ∀ᶠ n in atTop, 0 < κ (scale n) := by
    have hVpos : ∀ᶠ n in atTop, 0 < V (scale n) :=
      hscale.eventually hVreg.eventually_pos
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hVpos]
      with n hscalePos hVpos
    change 0 < stableScaleTime α ν (scale n)
    rw [stableScaleTime_eq_square_div_truncatedSecondMoment hscalePos hVpos]
    positivity
  have hblockDiv : Tendsto (fun n => (block n : ℝ) / κ (scale n))
      atTop (nhds constant) := by
    have hargDiv : Tendsto
        (fun n => (constant * κ (scale n)) / κ (scale n)) atTop
        (nhds constant) := by
      have heq : (fun n => (constant * κ (scale n)) / κ (scale n)) =ᶠ[atTop]
          fun _ => constant := by
        filter_upwards [hκScalePos] with n hκ
        field_simp [hκ.ne']
      exact tendsto_const_nhds.congr' heq.symm
    have hmul := hfloor.mul hargDiv
    have heq : (fun n => (block n : ℝ) / κ (scale n)) =ᶠ[atTop]
        fun n => (block n : ℝ) / (constant * κ (scale n)) *
          ((constant * κ (scale n)) / κ (scale n)) := by
      filter_upwards [hκScalePos] with n hκ
      field_simp [hκ.ne', hconstant.ne']
    simpa only [one_mul] using hmul.congr' heq.symm
  have hnormAtBlock : Tendsto
      (fun n => κ (normalization (block n)) / (block n : ℝ))
      atTop (nhds 1) := by
    have hnorm' := hnorm.2.2.comp hblockTop
    have hnorm'' : Tendsto
        (fun n => normalization (block n) ^ α /
          stableSlowVariation α ν (normalization (block n)) / (block n : ℝ))
        atTop (nhds 1) := by
      change Tendsto
        ((fun m : ℕ => normalization m ^ α /
          stableSlowVariation α ν (normalization m) / (m : ℝ)) ∘ block)
        atTop (nhds 1)
      exact hnorm'
    simpa only [κ, stableScaleTime] using hnorm''
  have hκBlockScale : Tendsto
      (fun n => κ (normalization (block n)) / κ (scale n))
      atTop (nhds constant) := by
    have hmul := hnormAtBlock.mul hblockDiv
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have heq : (fun n => κ (normalization (block n)) / (block n : ℝ) *
        ((block n : ℝ) / κ (scale n))) =ᶠ[atTop]
        fun n => κ (normalization (block n)) / κ (scale n) := by
      filter_upwards [hblockPos, hκScalePos] with n hn hκ
      field_simp [show (block n : ℝ) ≠ 0 by exact_mod_cast hn.ne', hκ.ne']
    simpa only [one_mul] using hmul.congr' heq
  have hVpos : ∀ᶠ n in atTop, 0 < V (scale n) :=
    hscale.eventually hVreg.eventually_pos
  have hVnormPos : ∀ᶠ n in atTop,
      0 < V (normalization (block n)) := by
    have hnormTop : Tendsto (fun n => normalization (block n)) atTop atTop :=
      hnorm.2.1.comp hblockTop
    exact hnormTop.eventually hVreg.eventually_pos
  have hquotient : Tendsto
      (fun n => normalization (block n) ^ 2 / V (normalization (block n)) /
        (scale n ^ 2 / V (scale n))) atTop (nhds constant) := by
    have heq : (fun n => normalization (block n) ^ 2 /
        V (normalization (block n)) /
        (scale n ^ 2 / V (scale n))) =ᶠ[atTop]
        fun n => κ (normalization (block n)) / κ (scale n) := by
      filter_upwards [hVpos, hVnormPos,
        hscale.eventually (eventually_gt_atTop 0),
        (hnorm.2.1.comp hblockTop).eventually (eventually_gt_atTop 0)]
        with n hVx hVy hx hy
      dsimp [κ]
      have hy' : 0 < normalization (block n) := by
        simpa only [Function.comp_apply] using hy
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hy' hVy,
        stableScaleTime_eq_square_div_truncatedSecondMoment hx hVx]
    have h := hκBlockScale.congr' heq.symm
    simpa [Real.rpow_one] using h
  have hrootPos : 0 < constant ^ (1 / α) :=
    Real.rpow_pos_of_pos hconstant _
  have hrootPower : (constant ^ (1 / α)) ^ α = constant := by
    rw [← Real.rpow_mul hconstant.le]
    rw [one_div_mul_cancel hα₀.ne', Real.rpow_one]
  have hquotient' : Tendsto
      (fun n => normalization (block n) ^ 2 / V (normalization (block n)) /
        (scale n ^ 2 / V (scale n))) atTop
        (nhds ((constant ^ (1 / α)) ^ (2 - β))) := by
    have hindex : 2 - β = α := by dsimp [β]; ring
    simpa only [hindex, hrootPower] using hquotient
  have hinverse := Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_squareQuotient_ratio
      hVreg hVmono hβ hβ₂ hrootPos hscale (hnorm.2.1.comp hblockTop) hquotient'
  simpa [block] using hinverse

end ProbabilityTheory

end

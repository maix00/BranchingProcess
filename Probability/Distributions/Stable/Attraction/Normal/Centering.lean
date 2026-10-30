/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import Probability.Distributions.Stable.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Analysis.Asymptotics.RegularVariation.AtZero.Potter
import Probability.Distributions.DomainOfAttraction.Centering
import Probability.Distributions.Moments.TailIntegrability
import Probability.Distributions.Stable.Attraction.Normal.Basic
import Probability.Distributions.Stable.Attraction.Normal.QuadraticTail
import Probability.Distributions.Stable.Attraction.Normal.CharacteristicTail
import Probability.Distributions.Moments.Truncated.RegularVariation

/-!
# Integrability and centering in the Gaussian domain of attraction

## Public declarations

- `IsInDomainOfAttractionAlong.integrable_id_of_gaussian` proves
  $\int |x|\,d\nu<\infty$ without assuming finite variance.
- `IsInDomainOfAttractionAlong.tendsto_scale_div_nat_of_gaussian` proves
  $a_n/n\to0$ for every Gaussian-domain normalization.
- `IsInDomainOfAttractionAlong.integral_eq_zero_of_gaussian` proves
  $\int x\,d\nu=0$ for an uncentered attraction to the standard Gaussian.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- Every law in the normal domain of attraction has a finite first absolute
moment. Gaussian attraction gives the quadratic-tail ratio limit; slow variation of
the truncated second moment and Potter's bound then make the integrated tail
finite. The normal-domain characterization is W. Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. II, 2nd ed. (Wiley, 1971),
Section XVII.5, Theorem 2 (ISBN 978-0-471-25709-7). -/
theorem IsInDomainOfAttractionAlong.integrable_id_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Integrable (id : ℝ → ℝ) ν := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  have hslow := h.truncatedSecondMoment_isSlowlyVarying_of_gaussian
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V 0 := by
    simpa [V] using hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Rpos, hRpos⟩ := eventually_atTop.1 hslow.eventually_pos
  let Rbase : ℝ := max Rpotter (max Rpos 1)
  have hRbasePos : 0 < Rbase := by dsimp [Rbase]; positivity
  have hRbasePotter : Rpotter ≤ Rbase := by
    dsimp [Rbase]
    exact le_max_left _ _
  have hRbaseMoment : Rpos ≤ Rbase := by
    dsimp [Rbase]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hVbase : 0 < V Rbase := hRpos Rbase hRbaseMoment
  let p : ℝ := 1 / 2
  let C : ℝ := V Rbase * 2 ^ p / Rbase ^ p
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hVbound : ∀ᶠ x : ℝ in atTop, V x ≤ C * x ^ p := by
    filter_upwards [eventually_ge_atTop Rbase] with x hx
    have hp := hpotter hRbasePotter hx
    have hratio : V x / V Rbase ≤ 2 ^ p * (x / Rbase) ^ p := by
      simpa [V, p, Real.rpow_zero] using hp
    have hmul : V x ≤ V Rbase * (2 ^ p * (x / Rbase) ^ p) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ hVbase).mp hratio
    have hdivpow : (x / Rbase) ^ p = x ^ p / Rbase ^ p :=
      Real.div_rpow (le_of_lt (lt_of_lt_of_le hRbasePos hx)) hRbasePos.le p
    have hpowPos : 0 < Rbase ^ p := Real.rpow_pos_of_pos hRbasePos p
    have heq : V Rbase * (2 ^ p * (x ^ p / Rbase ^ p)) = C * x ^ p := by
      dsimp [C]
      field_simp [hpowPos.ne']
    rw [hdivpow] at hmul
    rw [heq] at hmul
    exact hmul
  have htailRatio := h.tendsto_secondTailRatio_of_gaussian
  have htailSmall : ∀ᶠ x : ℝ in atTop, x ^ 2 * tail x / V x ≤ 1 := by
    have h := htailRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h] with x hx
    exact le_of_lt (by simpa [tail, V] using hx)
  have htailAntitone : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := ν)
    · intro y hy
      exact lt_of_le_of_lt hab hy
  have htailMeas : Measurable tail := htailAntitone.measurable
  obtain ⟨Rsmall, hRsmall⟩ := eventually_atTop.1 htailSmall
  obtain ⟨Rbound, hRbound⟩ := eventually_atTop.1 hVbound
  let R : ℝ := max Rbase (max Rsmall (max Rbound 1))
  have hRbaseLe : Rbase ≤ R := by
    dsimp [R]
    exact le_max_left _ _
  have hRsmallLe : Rsmall ≤ R := by
    dsimp [R]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRboundLe : Rbound ≤ R := by
    dsimp [R]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have htailBound : ∀ x, R ≤ x → tail x ≤ C * x ^ (p - 2) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
    have hVx : 0 < V x := lt_of_lt_of_le hVbase
      (truncatedSecondMoment_mono ν hRbasePos.le (le_trans hRbaseLe hx))
    have hratio := hRsmall x (le_trans hRsmallLe hx)
    have hVupper := hRbound x (le_trans hRboundLe hx)
    have htailV : x ^ 2 * tail x ≤ V x := by
      have := (div_le_iff₀ hVx).mp hratio
      nlinarith [mul_nonneg (sq_nonneg x) (measureReal_nonneg : 0 ≤ tail x)]
    have htailToV : tail x ≤ V x / x ^ 2 :=
      (le_div_iff₀ (sq_pos_of_pos hxpos)).2 (by simpa [mul_comm] using htailV)
    have hVToPower : V x / x ^ 2 ≤ C * x ^ (p - 2) := by
      calc
        V x / x ^ 2 ≤ (C * x ^ p) / x ^ 2 :=
          div_le_div_of_nonneg_right hVupper (sq_nonneg x)
        _ = C * x ^ (p - 2) := by
          rw [← Real.rpow_natCast x 2]
          rw [Real.rpow_sub hxpos p 2]
          field_simp [pow_ne_zero 2 hxpos.ne']
          ring_nf
    exact htailToV.trans hVToPower
  have hmajorant : IntegrableOn (fun x : ℝ => C * x ^ (p - 2)) (Ioi R) volume := by
    have hpow : p - 2 < -1 := by dsimp [p]; norm_num
    exact (integrableOn_Ioi_rpow_of_lt hpow hRpos).const_mul C
  have htailIntegrable : IntegrableOn tail (Ioi R) volume := by
    apply hmajorant.mono' htailMeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : 0 < x := lt_trans hRpos hx
    have hbound := htailBound x hx.le
    have htailNonneg : 0 ≤ tail x := by dsimp [tail]; exact measureReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg htailNonneg] using hbound
  have htailLocal : IntegrableOn tail (Ioc 0 R) volume := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top htailMeas.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg : 0 ≤ tail x)]
    have hmass : tail x ≤ 1 := by
      dsimp [tail]
      calc
        ν.real {y : ℝ | x < |y|} ≤ ν.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (by finiteness)
        _ = 1 := by simp
    exact hmass
  have htailZero : IntegrableOn tail (Ioi 0) volume := by
    have hset : Ioi R ∪ Ioc 0 R = Ioi 0 := by
      ext x
      simp only [mem_union, mem_Ioi, mem_Ioc]
      constructor
      · rintro (hx | ⟨hx, _⟩)
        · exact lt_trans hRpos hx
        · exact hx
      · intro hx
        by_cases hRx : R < x
        · exact Or.inl hRx
        · exact Or.inr ⟨hx, le_of_not_gt hRx⟩
    rw [← hset]
    exact htailIntegrable.union htailLocal
  simpa [tail] using integrable_id_of_integrableOn_twoSidedTail ν htailZero

/-- A Gaussian-domain normalization is sublinear, even without a finite
variance assumption. The Gaussian characteristic defect is regularly varying
at zero with index two and satisfies `n D(1/bₙ) → 1`. A Potter lower bound
gives `D(1/bₙ) ≤ C bₙ^(-3/2)`, which forces `bₙ / n → 0`. -/
theorem IsInDomainOfAttractionAlong.tendsto_scale_div_nat_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Tendsto (fun n : ℕ => scale n / (n : ℝ)) atTop (nhds 0) := by
  let D : ℝ → ℝ := fun u => 1 - ‖charFun ν u‖ ^ 2
  let hlimit : IsAlphaStable 2 (gaussianReal 0 1) :=
    (isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable
  have hdata := h.gaussian_defect_data
  have hpos := h.eventually_pos_normDefect_nhdsGT_zero hlimit
  have huniform := h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  have hpotter := Asymptotics.IsRegularlyVaryingAtZero.exists_potter_bound_of_uniform_ratio
    hpos huniform (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 2)
  obtain ⟨U, hUpos, hDpos, hbounds⟩ := hpotter
  let v : ℝ := U / 2
  have hvpos : 0 < v := by dsimp [v]; linarith
  have hvU : v < U := by dsimp [v]; linarith
  have hDv : 0 < D v := hDpos hvpos hvU
  let lower : ℝ := 1 / (2 * 2 ^ (2 - 1 / 2 : ℝ))
  have hlower : 0 < lower := by
    dsimp [lower]
    positivity
  let p : ℝ := 2 - 1 / 2
  let coeff : ℝ := lower * v ^ p
  have hcoeff : 0 < coeff := by
    dsimp [coeff]
    exact mul_pos hlower (Real.rpow_pos_of_pos hvpos p)
  let K : ℝ := D v / coeff
  have hK : 0 < K := div_pos hDv hcoeff
  have hscaleTop : Tendsto scale atTop atTop := hdata.2.1
  have hclock : Tendsto (fun n : ℕ => (n : ℝ) * D ((scale n)⁻¹))
      atTop (nhds 1) := by
    simpa [D] using hdata.2.2
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hscaleTop.eventually (eventually_gt_atTop 0)
  have hscaleLarge : ∀ᶠ n : ℕ in atTop, 1 / v ≤ scale n :=
    hscaleTop.eventually (eventually_ge_atTop (1 / v))
  have hclockLower : ∀ᶠ n : ℕ in atTop,
      1 / 2 < (n : ℝ) * D ((scale n)⁻¹) :=
    hclock.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hnatPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact_mod_cast hn
  have hDscalePos : ∀ᶠ n : ℕ in atTop, 0 < D ((scale n)⁻¹) := by
    filter_upwards [hscalePos, hscaleLarge] with n hsn hlarge
    have hu : 0 < (scale n)⁻¹ := inv_pos.mpr hsn
    have hvleDiv : 1 / scale n ≤ v := by
      apply (div_le_iff₀ hsn).2
      have hmul := (div_le_iff₀ hvpos).mp hlarge
      nlinarith [hmul]
    have hvle : (scale n)⁻¹ ≤ v := by simpa only [one_div] using hvleDiv
    have huU : (scale n)⁻¹ < U := by
      exact lt_of_le_of_lt hvle hvU
    simpa [D] using hDpos hu huU
  have hDscalePow : ∀ᶠ n : ℕ in atTop,
      D ((scale n)⁻¹) * (scale n) ^ p ≤ K := by
    filter_upwards [hscalePos, hscaleLarge, hDscalePos] with n hsn hlarge hDn
    have hu : 0 < (scale n)⁻¹ := inv_pos.mpr hsn
    have hvuDiv : 1 / scale n ≤ v := by
      apply (div_le_iff₀ hsn).2
      have hmul := (div_le_iff₀ hvpos).mp hlarge
      nlinarith [hmul]
    have hvu : (scale n)⁻¹ ≤ v := by simpa only [one_div] using hvuDiv
    have hpot := hbounds hu hvu hvU
    have hratio : lower * (v / (scale n)⁻¹) ^ p ≤ D v / D ((scale n)⁻¹) := by
      simpa [lower, p, D] using hpot.1
    have hinvEq : v / (scale n)⁻¹ = v * scale n := by
      rw [div_eq_mul_inv, inv_inv]
    have hmulPow : (v * scale n) ^ p = v ^ p * (scale n) ^ p :=
      Real.mul_rpow hvpos.le hsn.le
    have hratio' : lower * (v ^ p * (scale n) ^ p) ≤
        D v / D ((scale n)⁻¹) := by
      simpa [hinvEq, hmulPow] using hratio
    have hcross : coeff * (D ((scale n)⁻¹) * (scale n) ^ p) ≤ D v := by
      have := (le_div_iff₀ hDn).mp hratio'
      dsimp [coeff] at *
      nlinarith [this]
    exact (le_div_iff₀ hcoeff).2 (by simpa [K, mul_comm, mul_left_comm,
      mul_assoc] using hcross)
  have hscalePowPos : ∀ᶠ n : ℕ in atTop, 0 < (scale n) ^ p := by
    filter_upwards [hscalePos] with n hn
    exact Real.rpow_pos_of_pos hn p
  have hscalePowBound : ∀ᶠ n : ℕ in atTop,
      (scale n) ^ p ≤ 2 * K * (n : ℝ) := by
    filter_upwards [hclockLower, hDscalePow, hnatPos, hDscalePos,
      hscalePowPos] with n hclockN hDpow hn hDn hbp
    have hmul : (1 / 2) * (scale n) ^ p <
        ((n : ℝ) * D ((scale n)⁻¹)) * (scale n) ^ p :=
      mul_lt_mul_of_pos_right hclockN hbp
    have hupper : ((n : ℝ) * D ((scale n)⁻¹)) * (scale n) ^ p ≤
        (n : ℝ) * K := by
      calc
        _ = (n : ℝ) * (D ((scale n)⁻¹) * (scale n) ^ p) := by ring
        _ ≤ (n : ℝ) * K := mul_le_mul_of_nonneg_left hDpow hn.le
    have hcombined := hmul.trans_le hupper
    have hfinal : (scale n) ^ p < 2 * ((n : ℝ) * K) := by
      calc
        (scale n) ^ p = 2 * ((1 / 2 : ℝ) * (scale n) ^ p) := by ring
        _ < 2 * ((n : ℝ) * K) :=
          mul_lt_mul_of_pos_left hcombined (by norm_num)
    exact le_of_lt (by simpa [mul_comm, mul_left_comm, mul_assoc] using hfinal)
  have hsqrtInv : Tendsto (fun n : ℕ => (Real.sqrt (scale n))⁻¹)
      atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hscaleTop)
  have hupper : Tendsto (fun n : ℕ => 2 * K * (Real.sqrt (scale n))⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsqrtInv)
  have hratioBound : ∀ᶠ n : ℕ in atTop,
      scale n / (n : ℝ) ≤ 2 * K * (Real.sqrt (scale n))⁻¹ := by
    filter_upwards [hscalePowBound, hscalePos, hnatPos] with n hbp hsn hn
    have hsqrtPos : 0 < Real.sqrt (scale n) := Real.sqrt_pos.2 hsn
    have hpowEq : (scale n) ^ p = scale n * Real.sqrt (scale n) := by
      dsimp [p]
      rw [show (2 : ℝ) - (1 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by ring,
        Real.rpow_add hsn, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hdivBound : scale n / (n : ℝ) ≤
        2 * K / Real.sqrt (scale n) := by
      apply (div_le_iff₀ hn).2
      have hstep : scale n ≤ (2 * K * (n : ℝ)) / Real.sqrt (scale n) := by
        apply (le_div_iff₀ hsqrtPos).2
        simpa [hpowEq, mul_assoc, mul_left_comm, mul_comm] using hbp
      have hstep' : scale n ≤ (2 * K / Real.sqrt (scale n)) * (n : ℝ) := by
        calc
          scale n ≤ (2 * K * (n : ℝ)) / Real.sqrt (scale n) := hstep
          _ = (2 * K / Real.sqrt (scale n)) * (n : ℝ) := by
            field_simp [hsqrtPos.ne']
      exact hstep'
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdivBound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · filter_upwards [hscalePos, hnatPos] with n hsn hn
    exact div_nonneg hsn.le hn.le
  · exact hratioBound

/-- Uncentered Gaussian attraction forces zero mean. Its characteristic
defect first gives a sublinear normalization; Gaussian attraction also gives
the finite first moment, so the strong-law centering criterion applies. -/
theorem IsInDomainOfAttractionAlong.integral_eq_zero_of_gaussian
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale (fun _ => 0)) :
    (∫ x : ℝ, x ∂ν) = 0 := by
  exact integral_eq_zero_of_uncenteredAttraction_of_sublinearNormalization
    h h.integrable_id_of_gaussian h.tendsto_scale_div_nat_of_gaussian
end ProbabilityTheory

end

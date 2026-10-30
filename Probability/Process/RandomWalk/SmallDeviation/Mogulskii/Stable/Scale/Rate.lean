/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Inverse
public import Analysis.Asymptotics.RegularVariation.SlowScale
import Probability.Distributions.Moments.Truncated.RegularVariation

/-!
# Vanishing stable small-deviation rates

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.tendsto_stableSmallDeviationRate_zero_of_slowVariation`:
  if $a_n$ is a stable norming, $x_n\to\infty$, $x_n/a_n\to0$,
  $0<\alpha\le2$, and $L^*$ is slowly varying, then
  $x_n^\alpha/(nL^*(x_n))\to0$.
- `IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit`:
  under the two-scale condition and $L^*(u)\to\ell>0$, the rate tends to zero for every $\alpha>0$.
- `IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_const_mul_div`:
  for $c>0$, scaling the corridor by $c$ changes the asymptotic rate by the
  factor $c^\alpha$.

The two-scale hypothesis makes the small-deviation rate vanish throughout the
stable range `0 < α ≤ 2`. The slowly varying factor need not converge to a
finite limit: Potter bounds for the monotone truncated second moment are
enough, including the index-two case. A positive finite limit gives a separate
rate-vanishing result for every positive exponent. The Potter estimate is the
monotone form of Theorem 1.5.6 in N. H. Bingham, C. M. Goldie, and J. L.
Teugels, *Regular Variation*, Encyclopedia of Mathematics and its Applications
27, Cambridge University Press (1987), DOI 10.1017/CBO9780511721434. The
small-deviation rate considered here is the scale in Theorem 3, Section 4,
p. 764 of A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The stable small-deviation rate vanishes under the two-scale condition and
slow variation alone throughout `0 < α ≤ 2`. No finite positive limit of `L*`
is required. The proof uses the Potter upper bound for the truncated second
moment `V`; since `L*(x) = x^(α-2) V(x)`, the rate is bounded by a positive
power of `scale / normalization`. At `α = 2`, the regular-variation index of
`V` is zero, and the same Potter argument still applies. -/
theorem tendsto_stableSmallDeviationRate_zero_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hspaceTop : Tendsto scale atTop atTop)
    (hratio : Tendsto (fun n => scale n / normalization n) atTop (𝓝 0))
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Tendsto (stableSmallDeviationRate α ν scale) atTop (𝓝 0) := by
  classical
  let β : ℝ := 2 - α
  let δ : ℝ := α / 2
  let p : ℝ := β + δ
  let V : ℝ → ℝ := truncatedSecondMoment ν
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have htwoSubP : 2 - p = δ := by dsimp [p, β, δ]; ring
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V β := by
    simpa [V, β] using
      truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation hslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono hβ hδ
  let R : ℝ := Rpotter
  have hRpotterLe : Rpotter ≤ R := le_rfl
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hspaceTop.eventually (eventually_gt_atTop 0)
  have hnormPos : ∀ᶠ n in atTop, 0 < normalization n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact hnorm.1 n hn
  have hnormTop : Tendsto normalization atTop atTop := hnorm.2.1
  have hscaleAbove : ∀ᶠ n in atTop, R ≤ scale n :=
    hspaceTop.eventually (eventually_ge_atTop R)
  have hnormAbove : ∀ᶠ n in atTop, R ≤ normalization n :=
    hnormTop.eventually (eventually_ge_atTop R)
  have hVscalePos : ∀ᶠ n in atTop, 0 < V (scale n) := by
    filter_upwards [hspaceTop.eventually hVreg.eventually_pos] with n hn
    exact hn
  have hVnormPos : ∀ᶠ n in atTop, 0 < V (normalization n) := by
    filter_upwards [hnormTop.eventually hVreg.eventually_pos] with n hn
    exact hn
  have hratioPos : ∀ᶠ n in atTop, 0 < scale n / normalization n := by
    filter_upwards [hscalePos, hnormPos] with n hs hn
    exact div_pos hs hn
  have hratioLtOne : ∀ᶠ n in atTop, scale n / normalization n < 1 := by
    filter_upwards [hratio.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    exact hn
  have hscaleLtNorm : ∀ᶠ n in atTop, scale n < normalization n := by
    filter_upwards [hratioLtOne, hnormPos] with n hratioN hnormN
    have h := (div_lt_iff₀ hnormN).1 hratioN
    nlinarith
  have hnormTimeFactor : Tendsto
      (fun n => stableScaleTime α ν (normalization n) / (n : ℝ))
      atTop (𝓝 1) := by
    simpa [stableScaleTime] using hnorm.2.2
  have hnormTimeFactorLe : ∀ᶠ n in atTop,
      stableScaleTime α ν (normalization n) / (n : ℝ) ≤ 2 := by
    filter_upwards [hnormTimeFactor.eventually
      (isOpen_Iio.mem_nhds (by norm_num : (1 : ℝ) < 2))] with n hn
    exact hn.le
  have hratioPow : Tendsto
      (fun n => (scale n / normalization n) ^ δ) atTop (𝓝 0) :=
    hratio.rpow_const_nhds_zero hδ
  have hupperTendsto : Tendsto
      (fun n => ((2 : ℝ) * (2 : ℝ) ^ p) * (scale n / normalization n) ^ δ)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (2 : ℝ) * (2 : ℝ) ^ p) atTop
        (𝓝 ((2 : ℝ) * (2 : ℝ) ^ p))).mul hratioPow
  have hrateUpper : ∀ᶠ n in atTop,
      stableSmallDeviationRate α ν scale n ≤
        (2 * 2 ^ p) * (scale n / normalization n) ^ δ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hnormPos,
      hVscalePos, hVnormPos, hscaleAbove, hnormAbove, hscaleLtNorm,
      hratioPos, hnormTimeFactorLe] with n hn hs hb hVs hVb hsR hbR hslt hq hfactorLe
    have hVle : V (normalization n) / V (scale n) ≤
        2 ^ p * (normalization n / scale n) ^ p := by
      exact hpotter (le_trans hRpotterLe hsR) (le_of_lt hslt)
    have hqInv : normalization n / scale n = (scale n / normalization n)⁻¹ := by
      field_simp
    have hqPower : (scale n / normalization n) ^ (2 : ℕ) *
        (normalization n / scale n) ^ p =
        (scale n / normalization n) ^ δ := by
      rw [hqInv, Real.inv_rpow (le_of_lt hq)]
      rw [show (scale n / normalization n) ^ (2 : ℕ) =
          (scale n / normalization n) ^ (2 : ℝ) by
        exact (Real.rpow_natCast _ _).symm]
      rw [← Real.rpow_neg (le_of_lt hq), ← Real.rpow_add hq]
      congr 1
    have hslowScalePos : 0 < stableSlowVariation α ν (scale n) :=
      stableSlowVariation_pos hs hVs
    have hslowNormPos : 0 < stableSlowVariation α ν (normalization n) :=
      stableSlowVariation_pos hb hVb
    have hnRealPos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have htimeRatio :
        stableScaleTime α ν (scale n) /
            stableScaleTime α ν (normalization n) =
          (scale n / normalization n) ^ (2 : ℕ) *
            (V (normalization n) / V (scale n)) := by
      rw [stableScaleTime_eq_square_div_truncatedSecondMoment hs hVs,
        stableScaleTime_eq_square_div_truncatedSecondMoment hb hVb]
      dsimp [V]
      field_simp [ne_of_gt hs, ne_of_gt hb, ne_of_gt hVs, ne_of_gt hVb]
    have htimeRatioBound :
        stableScaleTime α ν (scale n) /
            stableScaleTime α ν (normalization n) ≤
          2 ^ p * (scale n / normalization n) ^ δ := by
      rw [htimeRatio]
      calc
        (scale n / normalization n) ^ (2 : ℕ) *
            (V (normalization n) / V (scale n)) ≤
          (scale n / normalization n) ^ (2 : ℕ) *
            (2 ^ p * (normalization n / scale n) ^ p) :=
          mul_le_mul_of_nonneg_left hVle (sq_nonneg _)
      _ = (2 : ℝ) ^ p * ((scale n / normalization n) ^ (2 : ℕ) *
            (normalization n / scale n) ^ p) := by ring
        _ = (2 : ℝ) ^ p * (scale n / normalization n) ^ δ := by rw [hqPower]
    have hrateAsTime : stableSmallDeviationRate α ν scale n =
        stableScaleTime α ν (scale n) / (n : ℝ) := by
      rw [stableSmallDeviationRate, stableScaleTime]
      field_simp [ne_of_gt hnRealPos, ne_of_gt hslowScalePos]
    have hκnormPos : 0 < stableScaleTime α ν (normalization n) :=
      div_pos (Real.rpow_pos_of_pos hb α) hslowNormPos
    have hrateEq : stableSmallDeviationRate α ν scale n =
        (stableScaleTime α ν (scale n) /
          stableScaleTime α ν (normalization n)) *
          (stableScaleTime α ν (normalization n) / (n : ℝ)) := by
      rw [hrateAsTime]
      field_simp [ne_of_gt hnRealPos, ne_of_gt hκnormPos]
    rw [hrateEq]
    calc
      (stableScaleTime α ν (scale n) /
          stableScaleTime α ν (normalization n)) *
          (stableScaleTime α ν (normalization n) / (n : ℝ)) ≤
        ((2 : ℝ) ^ p * (scale n / normalization n) ^ δ) * 2 := by
        have hκnormPos : 0 < stableScaleTime α ν (normalization n) :=
          div_pos (Real.rpow_pos_of_pos hb α) hslowNormPos
        have hfactorNonneg : 0 ≤
            stableScaleTime α ν (normalization n) / (n : ℝ) :=
          div_nonneg hκnormPos.le (Nat.cast_nonneg _)
        calc
          _ ≤ ((2 : ℝ) ^ p * (scale n / normalization n) ^ δ) *
              (stableScaleTime α ν (normalization n) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_right htimeRatioBound hfactorNonneg
          _ ≤ ((2 : ℝ) ^ p * (scale n / normalization n) ^ δ) * 2 :=
            mul_le_mul_of_nonneg_left hfactorLe (by positivity)
      _ = ((2 : ℝ) * (2 : ℝ) ^ p) *
          (scale n / normalization n) ^ δ := by ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperTendsto
  · filter_upwards [hscalePos, hVscalePos] with n hs hVs
    rw [stableSmallDeviationRate]
    have hslowPos : 0 < stableSlowVariation α ν (scale n) :=
      stableSlowVariation_pos hs hVs
    exact div_nonneg (Real.rpow_nonneg (le_of_lt hs) α)
      (mul_nonneg (Nat.cast_nonneg _) hslowPos.le)
  · exact hrateUpper

namespace IsStableMogulskiiScale

/-- For every positive exponent, the two-scale condition makes the
small-deviation rate vanish when `L*` has a positive finite limit. This covers
exponents above two as well, where the Potter-bound theorem does not apply. -/
theorem tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    {α ell : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hα : 0 < α) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) := by
  have hnormL : Tendsto
      (fun n => stableSlowVariation α ν (normalization n)) atTop (nhds ell) :=
    hslow.comp hscale.stableNorming.2.1
  have hscaleL : Tendsto
      (fun n => stableSlowVariation α ν (scale n)) atTop (nhds ell) :=
    hslow.comp hscale.scale_tendsto_atTop
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratioPow : Tendsto (fun n => (scale n / normalization n) ^ α)
      atTop (nhds 0) := hratio.rpow_const_nhds_zero hα
  have hnormFactor : Tendsto
      (fun n => normalization n ^ α /
        stableSlowVariation α ν (normalization n) / (n : ℝ))
      atTop (nhds 1) := hscale.stableNorming.2.2
  have hslowRatio : Tendsto
      (fun n => stableSlowVariation α ν (normalization n) /
        stableSlowVariation α ν (scale n)) atTop (nhds 1) := by
    have h := hnormL.div hscaleL hell.ne'
    have hfun : (fun n => stableSlowVariation α ν (normalization n)) /
        (fun n => stableSlowVariation α ν (scale n)) =
          (fun n => stableSlowVariation α ν (normalization n) /
            stableSlowVariation α ν (scale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hell.ne'] using h
  have hproduct : Tendsto
      (fun n => (scale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (scale n))) atTop (nhds 0) := by
    simpa using (hratioPow.mul hnormFactor).mul hslowRatio
  have hscalePos := hscale.eventually_scale_pos
  have hnormPos := hscale.eventually_normalization_pos
  have hnormLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (normalization n) := by
    filter_upwards [hnormL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have hscaleLPos : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) := by
    filter_upwards [hscaleL.eventually (Ioi_mem_nhds hell)] with n hn
    exact hn
  have heq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => (scale n / normalization n) ^ α *
        (normalization n ^ α /
          stableSlowVariation α ν (normalization n) / (n : ℝ)) *
        (stableSlowVariation α ν (normalization n) /
          stableSlowVariation α ν (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscalePos, hnormPos,
      hnormLPos, hscaleLPos] with n hn ha hb hLb hLa
    rw [stableSmallDeviationRate]
    rw [Real.div_rpow (le_of_lt ha) (le_of_lt hb) α]
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hbnNe : normalization n ≠ 0 := hb.ne'
    have haPowNe : scale n ^ α ≠ 0 := (Real.rpow_pos_of_pos ha α).ne'
    have hbPowNe : normalization n ^ α ≠ 0 := (Real.rpow_pos_of_pos hb α).ne'
    field_simp [hnNe, hbnNe, hLb.ne', hLa.ne', haPowNe, hbPowNe]
  exact hproduct.congr' heq.symm

/-- Rescaling a small-deviation argument by a fixed positive constant changes
the stable logarithmic rate by the corresponding regularly varying factor. -/
theorem tendsto_stableSmallDeviationRate_const_mul_div
    {α c : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hc : 0 < c) :
    Tendsto
      (fun n => stableSmallDeviationRate α ν (fun k => c * scale k) n /
        stableSmallDeviationRate α ν scale n)
      atTop (nhds (c ^ α)) := by
  let scaled : ℕ → ℝ := fun n => c * scale n
  have hscaled : IsStableMogulskiiScale α ν normalization scaled := by
    simpa [scaled] using hscale.const_mul hc
  have hratio :=
    ((stableScaleTime_isRegularlyVaryingAtTop hslow).ratio_tendsto hc).comp
      hscale.scale_tendsto_atTop
  have hnumL : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (scaled n) :=
    hscaled.scale_tendsto_atTop.eventually hslow.eventually_pos
  have hdenL : ∀ᶠ n : ℕ in atTop,
      0 < stableSlowVariation α ν (scale n) :=
    hscale.scale_tendsto_atTop.eventually hslow.eventually_pos
  have heq : (fun n => stableSmallDeviationRate α ν scaled n /
      stableSmallDeviationRate α ν scale n) =ᶠ[atTop]
      (fun n => stableScaleTime α ν (scaled n) /
        stableScaleTime α ν (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hnumL, hdenL]
      with n hn hnum hden
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [stableSmallDeviationRate, stableSmallDeviationRate,
      stableScaleTime, stableScaleTime]
    field_simp [hnNe, hnum.ne', hden.ne']
  exact hratio.congr' heq.symm


end IsStableMogulskiiScale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

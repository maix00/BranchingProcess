/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.BlockScale
public import Analysis.Asymptotics.RegularVariation.SlowScale
public import Analysis.Asymptotics.Scale.Scale
public import Probability.Distributions.Stable.Attraction
public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Distributions.Stable.Attraction.Norming.Inverse

/-!
# Two-scale condition for the stable Mogulskii route

Write $a_n$ for the corridor scale, $b_n$ for the stable normalization,
$L_\alpha^*$ for `stableSlowVariation α ν`, $T_\alpha(x)$ for
`stableScaleTime α ν x`, and $r_n$ for the stable small-deviation rate.
The public declarations are:

- `IsStableMogulskiiScale`: stable norming for $b_n$, together with
  $a_n\to\infty$ and $a_n/b_n\to0$.
- `IsStableMogulskiiScale.of_eventually_const_mul_normalization`,
  `IsStableMogulskiiScale.stableNorming`,
  `IsStableMogulskiiScale.scale_tendsto_atTop`,
  `IsStableMogulskiiScale.scale_div_normalization_tendsto_zero`,
  `IsStableMogulskiiScale.eventually_normalization_pos`,
  `IsStableMogulskiiScale.eventually_scale_pos`, and
  `IsStableMogulskiiScale.const_mul`:
  normalization and positive-rescaling rules for this two-scale condition.
- `IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier`
  and `IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier_of_eventually`:
  a diagonal $d_n\to\infty$ satisfies $d_na_n/b_n\to0$ and
  $T_\alpha(d_na_n)/(d_n^\alpha T_\alpha(a_n))\to1$, while the second
  theorem also retains fixed-parameter eventual events.
- `IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_two_zero` and
  `IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit`:
  $r_n\to0$ in the finite-variance and positive-limit regimes.
- `IsStableMogulskiiScale.eventually_scale_lt_normalization`,
  `IsStableMogulskiiScale.eventually_scale_pos_and_lt_normalization`, and
  `IsStableMogulskiiScale.eventually_slowVariation_pos`:
  eventually $0<a_n<b_n$ and $L_\alpha^*(a_n)>0$ under their hypotheses.
- `tendsto_stableSmallDeviationRate_const_mul_div`:
  $r_n(ca)/r_n(a)\to c^\alpha$ for $c>0$.

These scale relations serve Mogul'skii, *Small Deviations in a Space of
Trajectories*, Theorem 3, Section 4. Stable attraction and the one-block
corridor estimate remain separate hypotheses.


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory
open Asymptotics

/-! ## Stable scales -/

/-- The two-scale hypothesis used in the stable version of Mogulskii's
theorem.  `normalization` is the stable norming `bₙ`; `scale` is the smaller
corridor scale `aₙ`.  The stable law and the domain-of-attraction statement
are deliberately separate hypotheses and are not bundled into this
deterministic predicate.
-/
def IsStableMogulskiiScale
    (α : ℝ) (ν : Measure ℝ)
    (normalization scale : ℕ → ℝ) : Prop :=
  IsStableNorming α ν normalization ∧
    IsSmallDeviationScale scale normalization

namespace IsStableMogulskiiScale

/-- Replacing the raw domain-of-attraction normalization by an eventually
positive constant multiple preserves the two-scale hypothesis, provided the
replacement is already a stable norming for the same increment law. -/
theorem of_eventually_const_mul_normalization
    {α c : ℝ} {ν : Measure ℝ} {scale normalization normalization' : ℕ → ℝ}
    (hsmall : IsSmallDeviationScale scale normalization)
    (hnorm : IsStableNorming α ν normalization') (hc : 0 < c)
    (hnormalization_pos : ∀ᶠ n in atTop, 0 < normalization n)
    (hnormalization : normalization' =ᶠ[atTop]
      fun n => c * normalization n) :
    IsStableMogulskiiScale α ν normalization' scale :=
  ⟨hnorm, hsmall.of_eventually_const_mul hc hnormalization_pos hnormalization⟩

theorem stableNorming
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    IsStableNorming α ν normalization := h.1

theorem scale_tendsto_atTop
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    Tendsto scale atTop atTop := h.2.tendsto_atTop

theorem scale_div_normalization_tendsto_zero
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    Tendsto (fun n => scale n / normalization n) atTop (nhds 0) := h.2.tendsto_div

theorem eventually_normalization_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < normalization n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact h.1.1 n hn

theorem eventually_scale_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n :=
    h.2.eventually_pos

/-- A fixed positive multiple of a small-deviation scale is again a
small-deviation scale for the same stable norming. -/
theorem const_mul
    {α c : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) (hc : 0 < c) :
    IsStableMogulskiiScale α ν normalization (fun n => c * scale n) := by
  refine ⟨h.stableNorming,
    Asymptotics.IsSmallDeviationScale.of_tendsto ?_ ?_⟩
  · exact h.scale_tendsto_atTop.const_mul_atTop hc
  have hratio := h.scale_div_normalization_tendsto_zero.const_mul c
  simpa [div_eq_mul_inv, mul_assoc] using hratio

/-- Lemma 4's regular-variation transfer, with a multiplier chosen slowly
enough to remain negligible relative to the stable norming. The regular-
variation ratio is first proved for each fixed multiplier in the generic
asymptotic layer; diagonal selection then lets the multiplier tend to infinity.
-/
theorem exists_tendsto_slowStableScaleTime_multiplier
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    ∃ a : ℕ → ℝ, Monotone a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a n * (scale n / normalization n)) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (stableScaleTime α ν (a n * scale n) / stableScaleTime α ν (scale n)) /
          a n ^ α) atTop (nhds 1) := by
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratio_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ scale n / normalization n := by
    filter_upwards [hscale.eventually_scale_pos,
      hscale.eventually_normalization_pos] with n hs hn
    exact le_of_lt (div_pos hs hn)
  exact (stableScaleTime_isRegularlyVaryingAtTop hslow).exists_tendsto_slowScale
    hscale.scale_tendsto_atTop hratio hratio_nonneg

/-- Choose the single Lemma 4 diagonal that retains fixed-parameter
probability estimates as well as the regular-variation transfer for
`stableScaleTime`. The same parameter satisfies both source scale conditions.
-/
theorem exists_tendsto_slowStableScaleTime_multiplier_of_eventually
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {P : ℕ → ℕ → Prop}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hfixed : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n + 1) n) ∧
      Tendsto (fun n => ((d n : ℝ) + 1) * (scale n / normalization n))
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        (stableScaleTime α ν (((d n : ℝ) + 1) * scale n) /
          stableScaleTime α ν (scale n)) / (((d n : ℝ) + 1) ^ α))
        atTop (nhds 1) := by
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratio_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ scale n / normalization n := by
    filter_upwards [hscale.eventually_scale_pos,
      hscale.eventually_normalization_pos] with n hs hn
    exact le_of_lt (div_pos hs hn)
  exact Asymptotics.IsRegularlyVaryingAtTop.exists_tendsto_slowScale_of_eventually
    (stableScaleTime_isRegularlyVaryingAtTop hslow)
    hscale.scale_tendsto_atTop hratio hratio_nonneg hfixed

/-- For a finite-variance stable normalization, the original two-scale condition
`scale n / normalization n → 0` makes the exponent-two small-deviation rate tend to zero.  This identifies
the block length as negligible relative to the full time horizon in the Gaussian specialization. -/
theorem tendsto_stableSmallDeviationRate_two_zero
    {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto (stableSmallDeviationRate 2 ν scale) atTop (nhds 0) := by
  have hscaleMoment : Tendsto (fun n => stableSlowVariation 2 ν (scale n))
      atTop (nhds (∫ x, x ^ 2 ∂ν)) := by
    simpa only [Function.comp_def, stableSlowVariation_two] using
      (tendsto_truncatedSecondMoment ν hν).comp hscale.scale_tendsto_atTop
  have hscaleMomentPos : ∀ᶠ n in atTop, 0 < stableSlowVariation 2 ν (scale n) :=
    (hscale.scale_tendsto_atTop).eventually
      (eventually_stableSlowVariation_pos 2 ν hν hvariance)
  have hnormValuePos := hscale.eventually_normalization_pos
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratioSq : Tendsto (fun n => (scale n / normalization n) ^ 2)
      atTop (nhds 0) := by
    simpa only [pow_two, mul_zero] using hratio.mul hratio
  have hnormSqDiv := IsStableNorming.tendsto_sq_div_nat hν hscale.stableNorming
  have hrateFactor : Tendsto
      (fun n => (normalization n ^ 2 / (n : ℝ)) /
        stableSlowVariation 2 ν (scale n)) atTop (nhds 1) := by
    have h := hnormSqDiv.div hscaleMoment hvariance.ne'
    have hfun : (fun n => normalization n ^ 2 / (n : ℝ)) /
        (fun n => stableSlowVariation 2 ν (scale n)) =
          (fun n => (normalization n ^ 2 / (n : ℝ)) /
            stableSlowVariation 2 ν (scale n)) := by
      funext n
      rfl
    rw [hfun] at h
    simpa [hvariance.ne'] using h
  have hproduct : Tendsto
      (fun n => (scale n / normalization n) ^ 2 *
        ((normalization n ^ 2 / (n : ℝ)) /
          stableSlowVariation 2 ν (scale n))) atTop (nhds 0) := by
    simpa using hratioSq.mul hrateFactor
  have heq : stableSmallDeviationRate 2 ν scale =ᶠ[atTop]
      fun n => (scale n / normalization n) ^ 2 *
        ((normalization n ^ 2 / (n : ℝ)) /
          stableSlowVariation 2 ν (scale n)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscaleMomentPos,
      hnormValuePos] with n hn hscalePos hnormPos
    rw [stableSmallDeviationRate_two]
    rw [stableSlowVariation_two]
    have hnpos : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnormNe : normalization n ≠ 0 := hnormPos.ne'
    have hmomentNe : truncatedSecondMoment ν (scale n) ≠ 0 := by
      have hpos : 0 < stableSlowVariation 2 ν (scale n) := hscalePos
      simpa only [stableSlowVariation_two] using hpos.ne'
    field_simp [hnpos, hnormNe, hmomentNe]
  exact hproduct.congr' heq.symm

/-- For any positive stability index, the two-scale condition makes the
small-deviation rate vanish once `L*` has a positive finite limit.  This is the
general-index scale estimate; unlike the preceding Gaussian result, it does
not use a finite second moment of the increment law. -/
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

/-- The corridor scale is eventually strictly below the norming. This is the only
consequence of `a n / b n → 0` that the block argument uses. -/
theorem eventually_scale_lt_normalization
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, scale n < normalization n := by
  have hlt : ∀ᶠ n in atTop, scale n / normalization n < 1 :=
    (tendsto_order.1 h.scale_div_normalization_tendsto_zero).2 1 zero_lt_one
  filter_upwards [h.eventually_normalization_pos, hlt] with n hn hlt
  exact (div_lt_one hn).mp hlt

/-- The two scale facts the block argument uses together. -/
theorem eventually_scale_pos_and_lt_normalization
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale) :
    ∀ᶠ n in atTop, 0 < scale n ∧ scale n < normalization n :=
  h.eventually_scale_pos.and h.eventually_scale_lt_normalization

/-- `L*` is eventually positive along the corridor scale, so that the rate
`a n ^ α / (n * L* (a n))` has a nonvanishing denominator. -/
theorem eventually_slowVariation_pos
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    (h : IsStableMogulskiiScale α ν normalization scale)
    (hν : Integrable (fun x : ℝ => x ^ 2) ν) (hpos : 0 < ∫ x, x ^ 2 ∂ν) :
    ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) :=
  h.scale_tendsto_atTop.eventually (eventually_stableSlowVariation_pos α ν hν hpos)

end IsStableMogulskiiScale

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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

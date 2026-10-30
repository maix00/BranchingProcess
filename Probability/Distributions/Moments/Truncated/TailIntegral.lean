/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation.Integral.Tail
public import Probability.Distributions.Moments.Truncated.Layercake

import Probability.Distributions.Moments.TailIntegrability

import Analysis.Asymptotics.RegularVariation.AtZero.Potter
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Probability.Distributions.Moments.Truncated.TailAsymptotics
import Probability.Distributions.Moments.Truncated.RegularVariation

/-!
# Integrated tails of truncated second moments

This module relates the generic integrated-tail transforms to layer-cake
expressions for a probability law's truncated second moment.

## Public declarations

- `tendsto_radius_mul_discardedAbsFirstMoment_div_truncatedSecondMoment_zero`:
  if $V(x)=\int_{|y|\le x}y^2\,d\nu$ is slowly varying and
  $x^2\nu(|y|>x)/V(x)\to0$, then
  $x\int_{|y|>x}|y|\,d\nu/V(x)\to0$.
- `integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral` expresses `∫_{|x|>r}|x| μ(dx)` as `r μ(|x|>r)+∫_r^∞ μ(|x|>t)dt`.
- `firstTailIntegral_twoSidedTail_eq_half_truncatedSquareTailIntegral` identifies the first integrated two-sided tail with one half of the capped-square layer-cake integral.
- `secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral` identifies the twice-integrated tail with one half of the accumulated capped-square integral.
- `IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail`:
  for `0<α<2`, two-sided-tail regular variation of index `-α` is equivalent
  to regular variation of the accumulated capped-square tail with index
  `3-α`.
- `truncatedSecondMomentFactor_isSlowlyVarying_of_integratedTruncatedSquareTail`:
  regular variation of that accumulated tail implies slow variation of
  `u^(α-2)Vμ(u)`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory

/-- The first absolute moment beyond a threshold is the threshold times its
tail probability plus the integrated tail. This is the layer-cake formula
specialized to the indicator-truncated absolute value. -/
theorem integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (habsolute : Integrable (fun x : ℝ => |x|) μ)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    (∫ x, {y : ℝ | radius < |y|}.indicator (fun y => |y|) x ∂μ) =
      radius * μ.real {x : ℝ | radius < |x|} +
        ∫ t in Ioi radius, μ.real {x : ℝ | t < |x|} := by
  let tailSet : Set ℝ := {x : ℝ | radius < |x|}
  let tail : ℝ → ℝ := fun t => μ.real {x : ℝ | t < |x|}
  let f : ℝ → ℝ := tailSet.indicator (fun x => |x|)
  have htailSet : MeasurableSet tailSet := by
    dsimp [tailSet]
    exact measurableSet_lt measurable_const continuous_abs.measurable
  have hfInt : Integrable f μ := by
    dsimp [f]
    exact habsolute.indicator htailSet
  have hfNonneg : 0 ≤ᵐ[μ] f := by
    filter_upwards [] with x
    by_cases hx : x ∈ tailSet
    · simp [f, hx]
    · simp [f, hx]
  have hlayer := hfInt.integral_eq_integral_meas_lt hfNonneg
  have hmeasure (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      μ.real {x : ℝ | t < f x} = if t ≤ radius then tail radius else tail t := by
    have htpos : 0 < t := ht
    by_cases htr : t ≤ radius
    · have hset : {x : ℝ | t < f x} = tailSet := by
        ext x
        by_cases hx : x ∈ tailSet
        · have htAbs : t < |x| := lt_of_le_of_lt htr hx
          simp [f, hx, tailSet, htAbs]
        · have hx' : |x| ≤ radius := le_of_not_gt hx
          dsimp [f]
          rw [Set.indicator_of_notMem hx]
          change (t < 0) ↔ radius < |x|
          exact ⟨fun ht' => False.elim ((not_lt_of_ge htpos.le) ht'), fun hx'' =>
            False.elim (hx hx'')⟩
      rw [hset]
      simp [tail, tailSet, htr]
    · have hrt : radius < t := lt_of_not_ge htr
      have hset : {x : ℝ | t < f x} = {x : ℝ | t < |x|} := by
        ext x
        by_cases hx : x ∈ tailSet
        · simp [f, hx]
        · have hx' : |x| ≤ radius := le_of_not_gt hx
          dsimp [f]
          rw [Set.indicator_of_notMem hx]
          change (t < 0) ↔ t < |x|
          exact ⟨fun ht' => False.elim ((not_lt_of_ge htpos.le) ht'), fun ht' =>
            False.elim (not_lt_of_ge (le_trans hx' hrt.le) ht')⟩
      rw [hset]
      simp [tail, htr]
  have hlayer' :
      (∫ x, f x ∂μ) = ∫ t in Ioi (0 : ℝ),
        if t ≤ radius then tail radius else tail t := by
    calc
      (∫ x, f x ∂μ) =
          ∫ t in Ioi (0 : ℝ), μ.real {x : ℝ | t < f x} := hlayer
      _ = ∫ t in Ioi (0 : ℝ),
          if t ≤ radius then tail radius else tail t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact hmeasure t ht
  let boundedPart : Set ℝ := Ioc 0 radius
  let tailPart : Set ℝ := Ioi radius
  have hboundedPart : MeasurableSet boundedPart := measurableSet_Ioc
  have htailPart : MeasurableSet tailPart := measurableSet_Ioi
  have htailIntegrable := integrableOn_twoSidedTail_of_integrable_abs μ habsolute hradius
  have hboundedInt : Integrable (boundedPart.indicator (fun _ : ℝ => tail radius)) volume := by
    rw [integrable_indicator_iff hboundedPart]
    exact integrableOn_const (C := tail radius) (μ := volume) (s := boundedPart)
      (by simp [boundedPart])
  have htailPartInt : Integrable (tailPart.indicator tail) volume :=
    htailIntegrable.integrable_indicator htailPart
  have hdecomp (t : ℝ) :
      (Ioi (0 : ℝ)).indicator
          (fun t => if t ≤ radius then tail radius else tail t) t =
        boundedPart.indicator (fun _ => tail radius) t +
          tailPart.indicator tail t := by
    by_cases ht0 : 0 < t
    · by_cases htr : t ≤ radius
      · have hmem : t ∈ boundedPart := ⟨ht0, htr⟩
        have hnot : t ∉ tailPart := by simp [tailPart, not_lt.mpr htr]
        rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) by simpa using ht0)]
        simp [hmem, hnot, htr]
      · have hrt : radius < t := lt_of_not_ge htr
        have hmem : t ∈ tailPart := by simp [tailPart, hrt]
        have hnot : t ∉ boundedPart := by simp [boundedPart, not_le_of_gt hrt]
        rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) by simpa using ht0)]
        simp [hmem, hnot, htr]
    · have hnotBounded : t ∉ boundedPart := by
        simp [boundedPart, not_lt.mpr (le_of_not_gt ht0)]
      have hnotTail : t ∉ tailPart := by
        have htle : t ≤ 0 := le_of_not_gt ht0
        simp [tailPart, not_lt.mpr (le_trans htle hradius)]
      rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) by simpa using ht0)]
      simp [hnotBounded, hnotTail]
  have hsplit :
      (∫ t in Ioi (0 : ℝ), if t ≤ radius then tail radius else tail t) =
        radius * tail radius + ∫ t in Ioi radius, tail t := by
    calc
      (∫ t in Ioi (0 : ℝ), if t ≤ radius then tail radius else tail t) =
          ∫ t, (Ioi (0 : ℝ)).indicator
            (fun t => if t ≤ radius then tail radius else tail t) t :=
          (integral_indicator measurableSet_Ioi).symm
      _ = ∫ t, (boundedPart.indicator (fun _ => tail radius) t +
          tailPart.indicator tail t) := by
            apply integral_congr_ae
            exact ae_of_all _ hdecomp
      _ = (∫ t, boundedPart.indicator (fun _ : ℝ => tail radius) t) +
          ∫ t, tailPart.indicator tail t := integral_add hboundedInt htailPartInt
      _ = radius * tail radius + ∫ t in Ioi radius, tail t := by
          have hA : (∫ t, boundedPart.indicator (fun _ : ℝ => tail radius) t) =
              radius * tail radius := by
            rw [integral_indicator_const (tail radius) hboundedPart]
            simp only [smul_eq_mul]
            simp [boundedPart, hradius]
          have hB : (∫ t, tailPart.indicator tail t) =
              ∫ t in Ioi radius, tail t := integral_indicator htailPart
          rw [hA, hB]
  calc
    (∫ x, {y : ℝ | radius < |y|}.indicator (fun y => |y|) x ∂μ) =
        ∫ x, f x ∂μ := by rfl
    _ = ∫ t in Ioi (0 : ℝ),
        if t ≤ radius then tail radius else tail t := hlayer'
    _ = radius * tail radius + ∫ t in Ioi radius, tail t := hsplit
    _ = _ := by rfl

/-- The first integrated two-sided tail is half the layer-cake integral for
 the capped square. The substitution `s = t²` converts the square-tail
 representation to the usual absolute-value tail. -/
theorem firstTailIntegral_twoSidedTail_eq_half_truncatedSquareTailIntegral
    (μ : Measure ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Asymptotics.firstTailIntegral (fun t => μ.real {x : ℝ | t < |x|}) u =
      (1 / 2 : ℝ) * truncatedSquareTailIntegral μ u := by
  let g : ℝ → ℝ := fun s => μ.real {x : ℝ | s < x ^ 2}
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := u)
    (f := fun t : ℝ => t ^ 2) (f' := fun t => 2*t)
    (g := g) (by fun_prop)
    (by
      intro t ht
      simpa using hasDerivAt_pow 2 t)
    (by
      intro t ht
      have ht0 : 0 < t := by simpa [min_eq_left hu] using ht.1
      exact mul_nonneg (by norm_num) ht0.le)
  have htailEq : EqOn (fun t : ℝ => g (t ^ 2) * (2*t))
      (fun t => 2 * (t * μ.real {x : ℝ | t < |x|})) (uIcc 0 u) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le hu] at ht
      exact ht.1
    have hset : {x : ℝ | t ^ 2 < x ^ 2} = {x : ℝ | t < |x|} := by
      ext x
      constructor
      · intro hx
        exact (sq_lt_sq₀ ht0 (abs_nonneg x)).1 (by simpa [sq_abs] using hx)
      · intro hx
        have hs := (sq_lt_sq₀ ht0 (abs_nonneg x)).2 hx
        simpa [sq_abs] using hs
    change μ.real {x : ℝ | t ^ 2 < x ^ 2} * (2*t) = _
    rw [hset]
    ring
  have hleft :
      (∫ t in (0:ℝ)..u, g (t ^ 2) * (2*t)) =
        2 * Asymptotics.firstTailIntegral
          (fun t => μ.real {x : ℝ | t < |x|}) u := by
    calc
      (∫ t in (0:ℝ)..u, g (t ^ 2) * (2*t)) =
          ∫ t in (0:ℝ)..u, 2 * (t * μ.real {x : ℝ | t < |x|}) :=
            intervalIntegral.integral_congr htailEq
      _ = 2 * Asymptotics.firstTailIntegral
          (fun t => μ.real {x : ℝ | t < |x|}) u := by
            rw [intervalIntegral.integral_const_mul]
            simp [Asymptotics.firstTailIntegral, max_eq_left hu]
  have hright :
      (∫ s in (0:ℝ)..u ^ 2, g s) = truncatedSquareTailIntegral μ u := by
    simpa [g] using (truncatedSquareTailIntegral_eq_intervalIntegral μ hu).symm
  have hsub' :
      (∫ t in (0:ℝ)..u, g (t ^ 2) * (2*t)) = truncatedSquareTailIntegral μ u := by
    have hsub'' :
        (∫ t in (0:ℝ)..u, g (t ^ 2) * (2*t)) =
          ∫ s in (0:ℝ)..u ^ 2, g s := by
      simpa using hsub
    rw [hright] at hsub''
    exact hsub''
  rw [hleft] at hsub'
  linarith

/-- The twice-integrated two-sided tail equals half the accumulated capped
square-tail integral. -/
theorem secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral
    (μ : Measure ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Asymptotics.secondTailIntegral (fun t => μ.real {x : ℝ | t < |x|}) u =
      (1 / 2 : ℝ) *
        (∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t) := by
  have hEq : EqOn
      (fun t : ℝ => Asymptotics.firstTailIntegral
        (fun s => μ.real {x : ℝ | s < |x|}) t)
      (fun t => (1 / 2 : ℝ) * truncatedSquareTailIntegral μ t)
      (uIcc 0 u) := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [Set.uIcc_of_le hu] at ht
      exact ht.1
    exact firstTailIntegral_twoSidedTail_eq_half_truncatedSquareTailIntegral μ ht0
  calc
    Asymptotics.secondTailIntegral (fun t => μ.real {x : ℝ | t < |x|}) u =
        ∫ t in (0:ℝ)..u, (1 / 2 : ℝ) * truncatedSquareTailIntegral μ t :=
      intervalIntegral.integral_congr hEq
    _ = (1 / 2 : ℝ) *
        (∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t) := by
      rw [intervalIntegral.integral_const_mul]

/-- For a probability law and `0 < α < 2`, regular variation of its two-sided
 tail is equivalent to regular variation of the accumulated layer-cake
 truncated-square tail. -/
theorem IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsRegularlyVaryingAtTop
        (fun u : ℝ => μ.real {x : ℝ | u < |x|}) (-α) ↔
      Asymptotics.IsRegularlyVaryingAtTop
        (fun u : ℝ => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t)
        (3 - α) := by
  let H : ℝ → ℝ := fun u => μ.real {x : ℝ | u < |x|}
  let J : ℝ → ℝ := fun u => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t
  change Asymptotics.IsRegularlyVaryingAtTop H (-α) ↔
    Asymptotics.IsRegularlyVaryingAtTop J (3 - α)
  have hanti : Antitone H := by
    intro x y hxy
    apply measureReal_mono (μ := μ)
      (s₁ := {z : ℝ | y < |z|}) (s₂ := {z : ℝ | x < |z|})
    · intro z hz
      exact lt_of_le_of_lt hxy hz
  have hnonneg : ∀ x, 0 ≤ H x := fun _ => measureReal_nonneg
  have hleOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → H x ≤ 1 := by
    intro x _
    exact measureReal_le_one
  have hHint : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * H t) volume a b := by
    intro a b
    exact hanti.intervalIntegrable.continuousOn_mul continuousOn_id
  have htailIff := Asymptotics.IsRegularlyVaryingAtTop.secondTailIntegral_iff
    hα₀ hα₂ hanti hnonneg hleOne hHint
  have hconstHalf : Asymptotics.IsRegularlyVaryingAtTop
      (fun _ : ℝ => (1 / 2 : ℝ)) 0 := by
    refine ⟨Filter.Eventually.of_forall (by norm_num), ?_⟩
    intro c hc
    have heq : (fun _ : ℝ => ((1 / 2 : ℝ) / (1 / 2 : ℝ))) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [] with x
      norm_num
    simp [Real.rpow_zero]
  have hconstTwo := hconstHalf.inv
  have hsecondEq :
      Asymptotics.secondTailIntegral H =ᶠ[atTop] fun u => (1 / 2 : ℝ) * J u := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    exact secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral
      μ hu
  have hJtoSecond :
      Asymptotics.IsRegularlyVaryingAtTop J (3 - α) →
        Asymptotics.IsRegularlyVaryingAtTop
          (Asymptotics.secondTailIntegral H) (3 - α) := by
    intro hJ
    have hmul := hconstHalf.mul hJ
    simpa [zero_add, neg_zero] using hmul.congr hsecondEq.symm
  have hSecondToJ :
      Asymptotics.IsRegularlyVaryingAtTop
          (Asymptotics.secondTailIntegral H) (3 - α) →
        Asymptotics.IsRegularlyVaryingAtTop J (3 - α) := by
    intro hSecond
    have hscale := hconstTwo.mul hSecond
    have hEq : (fun u : ℝ => (1 / 2 : ℝ)⁻¹ *
        Asymptotics.secondTailIntegral H u) =ᶠ[atTop] J := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
      have h : Asymptotics.secondTailIntegral H u = (1 / 2 : ℝ) * J u := by
        simpa [H, J] using
          secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral
            μ hu
      rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num, h]
      field_simp
    simpa [zero_add, neg_zero] using hscale.congr hEq
  constructor
  · intro hH
    exact hSecondToJ (htailIff.mp hH)
  · intro hJ
    exact htailIff.mpr (hJtoSecond hJ)

/-- Regular variation of the integrated capped-square tail implies slow
variation of the normalized truncated second moment. This packages the
measure-theoretic part of the inverse-Tauberian route after tail regular
variation has been obtained. -/
theorem truncatedSecondMomentFactor_isSlowlyVarying_of_integratedTruncatedSquareTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hIntegral : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t)
      (3 - α)) :
    Asymptotics.IsSlowlyVaryingAtTop
      (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment μ u) := by
  let T : ℝ → ℝ := fun u => μ.real {x : ℝ | u < |x|}
  let R : ℝ → ℝ := fun u => truncatedSecondMoment μ u / (u ^ 2 * T u)
  have hTail : Asymptotics.IsRegularlyVaryingAtTop T (-α) := by
    exact (ProbabilityTheory.IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail
      μ hα₀ hα₂).mpr hIntegral
  have hTailFactor : Asymptotics.IsSlowlyVaryingAtTop
      (fun u : ℝ => u ^ α * T u) := by
    simpa [Asymptotics.IsSlowlyVaryingAtTop, T, mul_comm] using
      hTail.mul (Asymptotics.IsRegularlyVaryingAtTop.rpow α)
  have hratio : Tendsto R atTop (nhds (α / (2 - α))) := by
    simpa [R, T] using
      tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying μ hα₀ hα₂ hTail
  have hratioSlow : Asymptotics.IsSlowlyVaryingAtTop R :=
    Asymptotics.IsSlowlyVaryingAtTop.of_tendsto_pos
      (div_pos hα₀ (by linarith)) hratio
  have hfactorEq : (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment μ u) =ᶠ[atTop]
      fun u => (u ^ α * T u) * R u := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hTail.eventually_pos] with u hu hTu
    have hpow : u ^ (α - 2) = u ^ α / u ^ 2 := by
      calc
        u ^ (α - 2) = u ^ α / u ^ (2:ℝ) := Real.rpow_sub hu α 2
        _ = u ^ α / u ^ 2 := congrArg (fun z : ℝ => u ^ α / z)
          (Real.rpow_natCast u 2)
    have hden : u ^ 2 * T u ≠ 0 := ne_of_gt (mul_pos (sq_pos_of_pos hu) hTu)
    change u ^ (α - 2) * truncatedSecondMoment μ u = _
    rw [hpow]
    dsimp [R]
    field_simp [hden]
  have hprod := hTailFactor.mul hratioSlow
  refine ⟨?_, ?_⟩
  · filter_upwards [hfactorEq, hprod.eventually_pos] with u hEq hpos
    rw [hEq]
    exact hpos
  · intro c hc
    have hcTop : Tendsto (fun u : ℝ => c * u) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hfactorScaled : (fun u : ℝ =>
        (c * u) ^ (α - 2) * truncatedSecondMoment μ (c * u) /
          (u ^ (α - 2) * truncatedSecondMoment μ u)) =ᶠ[atTop]
        fun u => (((c * u) ^ α * T (c * u)) * R (c * u)) /
          ((u ^ α * T u) * R u) := by
      filter_upwards [hfactorEq, hcTop.eventually hfactorEq] with u hEq hEqc
      rw [hEqc, hEq]
    exact (hprod.ratio_tendsto hc).congr' hfactorScaled.symm

/-- The quadratic-tail ratio bound and Potter's estimate make the integrated
tail beyond a large cutoff negligible compared with `V(x) / x`. The exponent
`1/2` in Potter's envelope is chosen only to make the resulting power
integrable. -/
private lemma tendsto_tailIntegral_div_truncatedSecondMoment_mul_radius_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (habsolute : Integrable (fun x : ℝ => |x|) ν)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν))
    (hFeller : Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) :
    Tendsto (fun x : ℝ => x *
      (∫ t in Ioi x, ν.real {y : ℝ | t < |y|}) /
        truncatedSecondMoment ν x) atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment ν
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let p : ℝ := 1 / 2
  have hVreg : Asymptotics.IsRegularlyVaryingAtTop V 0 := by
    simpa [V] using hVslow
  have hVmono : Asymptotics.IsEventuallyMonotoneAtTop V := by
    simpa [V] using truncatedSecondMoment_isEventuallyMonotone ν
  obtain ⟨Rpotter, hRpotter, hpotter⟩ :=
    hVreg.exists_potter_upper_bound hVmono (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : 0 < p)
  obtain ⟨Rpositive, hRpositive⟩ := eventually_atTop.1 hVslow.1
  have htailIntegrable : IntegrableOn tail (Ioi (0 : ℝ)) volume := by
    simpa [tail] using integrableOn_twoSidedTail_of_integrable_abs ν habsolute
      (by norm_num : (0 : ℝ) ≤ 0)
  have htailAntitone : Antitone tail := by
    intro a b hab
    apply measureReal_mono (μ := ν)
    · intro y hy
      exact lt_of_le_of_lt hab hy
  have htailMeasurable : Measurable tail := htailAntitone.measurable
  have hfactor : (2 : ℝ) ^ p ≤ 2 := by
    have hp : p ≤ 1 := by dsimp [p]; norm_num
    simpa [p, Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp)
  have hFellerEventually (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ x : ℝ in atTop,
        x ^ 2 * tail x / V x ≤ ε := by
    filter_upwards [hFeller.eventually (Iio_mem_nhds hε)] with x hx
    exact le_of_lt (by simpa [tail, V] using hx)
  have hIntegralBound (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ x : ℝ in atTop,
        (∫ t in Ioi x, tail t) ≤ 4 * ε * V x / x := by
    obtain ⟨RFeller, hRFeller⟩ := eventually_atTop.1 (hFellerEventually ε hε)
    let R : ℝ := max 1 (max Rpotter (max Rpositive RFeller))
    have hRpos : 0 < R := by dsimp [R]; positivity
    have hRpotterLe : Rpotter ≤ R := by
      dsimp [R]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hRpositiveLe : Rpositive ≤ R := by
      dsimp [R]
      exact le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hRFellerLe : RFeller ≤ R := by
      dsimp [R]
      exact le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))
    have hVpos : ∀ ⦃x : ℝ⦄, R ≤ x → 0 < V x := by
      intro x hx
      exact hRpositive x (le_trans hRpositiveLe hx)
    have hFellerSmall : ∀ ⦃x : ℝ⦄, R ≤ x → x ^ 2 * tail x / V x ≤ ε := by
      intro x hx
      exact hRFeller x (le_trans hRFellerLe hx)
    have hPotter : ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y →
        V y / V x ≤ 2 ^ p * (y / x) ^ p := by
      intro x y hx hxy
      simpa [p] using hpotter (le_trans hRpotterLe hx) hxy
    have hbound (x t : ℝ) (hx : R ≤ x) (ht : x < t) :
        tail t ≤ (2 * ε * V x / x ^ p) * t ^ (p - 2) := by
      have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
      have htpos : 0 < t := lt_trans hxpos ht
      have hxSq : 0 < x ^ 2 := sq_pos_of_pos hxpos
      have htSq : 0 < t ^ 2 := sq_pos_of_pos htpos
      have hVx : 0 < V x := hVpos hx
      have hVt : 0 < V t := hVpos (le_trans hx ht.le)
      have hratio := hPotter hx ht.le
      have hratioNonneg : 0 ≤ (t / x) ^ p :=
        Real.rpow_nonneg (div_nonneg htpos.le hxpos.le) p
      have hratioBound : V t ≤ 2 * V x * (t / x) ^ p := by
        have hratio' : V t ≤ V x * (2 ^ p * (t / x) ^ p) := by
          simpa [mul_comm] using (div_le_iff₀ hVx).mp hratio
        calc
          V t ≤ V x * (2 ^ p * (t / x) ^ p) := hratio'
          _ ≤ V x * (2 * (t / x) ^ p) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hfactor hratioNonneg) hVx.le
          _ = 2 * V x * (t / x) ^ p := by ring
      have hF := hFellerSmall (le_trans hx ht.le)
      have hF' : t ^ 2 * tail t ≤ ε * V t :=
        (div_le_iff₀ hVt).mp hF
      have htail' : tail t ≤ ε * V t / t ^ 2 :=
        (le_div_iff₀ htSq).2 (by simpa [mul_comm] using hF')
      have htail'' : tail t ≤ ε * (2 * V x * (t / x) ^ p) / t ^ 2 :=
        htail'.trans (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratioBound hε.le) htSq.le)
      have hdivPow : (t / x) ^ p = t ^ p / x ^ p :=
        Real.div_rpow htpos.le hxpos.le p
      have hpowSub : t ^ p / t ^ (2 : ℕ) = t ^ (p - 2) := by
        rw [← Real.rpow_natCast t 2]
        exact (Real.rpow_sub htpos p 2).symm
      have hxpow : 0 < x ^ p := Real.rpow_pos_of_pos hxpos p
      have hteq : ε * (2 * V x * (t / x) ^ p) / t ^ 2 =
          (2 * ε * V x / x ^ p) * t ^ (p - 2) := by
        calc
          _ = (2 * ε * V x / x ^ p) * (t ^ p / t ^ 2) := by
            rw [hdivPow]
            field_simp [ne_of_gt hxpow, ne_of_gt htSq]
          _ = _ := by rw [hpowSub]
      exact htail''.trans_eq hteq
    filter_upwards [eventually_ge_atTop R] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
    have hVx : 0 < V x := hVpos hx
    have hC : 0 ≤ 2 * ε * V x / x ^ p :=
      div_nonneg (by positivity) (Real.rpow_pos_of_pos hxpos p).le
    have htailX : IntegrableOn tail (Ioi x) volume :=
      htailIntegrable.mono_set (Ioi_subset_Ioi hxpos.le)
    have hpowInt : IntegrableOn (fun t : ℝ => t ^ (p - 2)) (Ioi x) volume :=
      integrableOn_Ioi_rpow_of_lt (by dsimp [p]; norm_num) hxpos
    have hmajorInt : IntegrableOn
        (fun t : ℝ => (2 * ε * V x / x ^ p) * t ^ (p - 2)) (Ioi x) volume :=
      hpowInt.const_mul _
    have hmonoIntegral := setIntegral_mono_on htailX hmajorInt measurableSet_Ioi
      (fun t ht => hbound x t hx ht)
    calc
      (∫ t in Ioi x, tail t) ≤
          ∫ t in Ioi x, (2 * ε * V x / x ^ p) * t ^ (p - 2) := hmonoIntegral
      _ = (2 * ε * V x / x ^ p) *
          (∫ t in Ioi x, t ^ (p - 2)) := by rw [integral_const_mul]
      _ = (2 * ε * V x / x ^ p) *
          (-x ^ (p - 2 + 1) / (p - 2 + 1)) := by
        rw [integral_Ioi_rpow_of_lt (by dsimp [p]; norm_num) hxpos]
      _ = 4 * ε * V x / x := by
        have hp : p = 1 / 2 := rfl
        subst p
        have hpow : x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
          rw [← Real.rpow_add hxpos]
          rw [show (-(1 / 2 : ℝ)) + -(1 / 2 : ℝ) = -1 by ring,
            Real.rpow_neg_one]
        have hcoef : -x ^ (-(1 / 2 : ℝ)) / (-(1 / 2 : ℝ)) =
            2 * x ^ (-(1 / 2 : ℝ)) := by
          field_simp
        rw [show (1 / 2 : ℝ) - 2 + 1 = -(1 / 2 : ℝ) by ring, hcoef]
        rw [div_eq_mul_inv]
        calc
          (2 * ε * V x * (x ^ (1 / 2 : ℝ))⁻¹) *
              (2 * x ^ (-(1 / 2 : ℝ))) =
              4 * ε * V x * ((x ^ (1 / 2 : ℝ))⁻¹ *
                (x ^ (1 / 2 : ℝ))⁻¹) := by
            rw [Real.rpow_neg hxpos.le]
            ring
          _ = 4 * ε * V x *
              (x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))) := by
                rw [← Real.rpow_neg hxpos.le]
          _ = 4 * ε * V x * x⁻¹ := by rw [hpow]
          _ = 4 * ε * V x / x := by rw [div_eq_mul_inv]
  have hVpos : ∀ᶠ x : ℝ in atTop, 0 < V x := hVslow.1
  have hVpositive : ∀ᶠ x : ℝ in atTop, V x ≠ 0 := hVpos.mono fun x hx => hx.ne'
  have htailNonneg : ∀ x, 0 ≤ ∫ t in Ioi x, tail t := by
    intro x
    exact setIntegral_nonneg measurableSet_Ioi fun t _ => measureReal_nonneg
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos] with x hx hVx
    have hnonneg : 0 ≤ x * (∫ t in Ioi x, tail t) / V x :=
      div_nonneg (mul_nonneg hx.le (htailNonneg x)) hVx.le
    linarith
  · intro ε hε
    let η : ℝ := ε / 8
    have hη : 0 < η := by dsimp [η]; linarith
    have hFsmall : ∀ᶠ x : ℝ in atTop,
        x ^ 2 * tail x / V x < ε / 2 :=
      hFeller.eventually (Iio_mem_nhds (by linarith))
    have hIbound := hIntegralBound η hη
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVpos, hFsmall, hIbound]
      with x hx hVx hFx hIx
    have hterm : x * (∫ t in Ioi x, tail t) / V x ≤ 4 * η := by
      apply (div_le_iff₀ hVx).2
      calc
        x * (∫ t in Ioi x, tail t) ≤
            x * (4 * η * V x / x) :=
          mul_le_mul_of_nonneg_left hIx hx.le
        _ = 4 * η * V x := by field_simp [hx.ne']
    have hdecomp :
        x * (∫ t in Ioi x, tail t) / V x ≤ ε / 2 := by
      dsimp [η] at hterm
      linarith
    exact hdecomp.trans_lt (by linarith)

/-- In the Gaussian domain of attraction, the discarded absolute first moment
is negligible relative to the cutoff and its truncated second moment. This
combines the quadratic-tail ratio limit with the integrated-tail estimate
above and the layer-cake identity. -/
theorem tendsto_radius_mul_discardedAbsFirstMoment_div_truncatedSecondMoment_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (habsolute : Integrable (fun x : ℝ => |x|) ν)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment ν))
    (hFeller : Tendsto
      (fun x : ℝ => x ^ 2 * ν.real {y : ℝ | x < |y|} /
        truncatedSecondMoment ν x) atTop (nhds 0)) :
    Tendsto (fun x : ℝ => x *
      (∫ y, {z : ℝ | x < |z|}.indicator (fun z => |z|) y ∂ν) /
        truncatedSecondMoment ν x) atTop (nhds 0) := by
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let tailIntegral : ℝ → ℝ := fun x => ∫ t in Ioi x, tail t
  have hintegral := tendsto_tailIntegral_div_truncatedSecondMoment_mul_radius_zero
    habsolute hVslow hFeller
  have hsum : Tendsto (fun x : ℝ =>
      x ^ 2 * tail x / truncatedSecondMoment ν x +
        x * tailIntegral x / truncatedSecondMoment ν x)
      atTop (nhds (0 + 0)) := by
    simpa [tail, tailIntegral] using hFeller.add hintegral
  have heq : (fun x : ℝ => x *
      (∫ y, {z : ℝ | x < |z|}.indicator (fun z => |z|) y ∂ν) /
        truncatedSecondMoment ν x) =ᶠ[atTop]
      fun x => x ^ 2 * tail x / truncatedSecondMoment ν x +
        x * tailIntegral x / truncatedSecondMoment ν x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hVslow.1] with x hx hVx
    have hlayer := integral_indicator_abs_eq_radius_mul_tail_add_tailIntegral
      ν habsolute hx.le
    dsimp [tail, tailIntegral]
    rw [hlayer]
    field_simp [ne_of_gt hVx]
  simpa using hsum.congr' heq.symm

end ProbabilityTheory

end

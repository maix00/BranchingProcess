/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation.TailIntegral
public import Probability.Distributions.Moments.Truncated

/-!
# Integrated tails of truncated second moments

This module relates the generic integrated-tail transforms to layer-cake
expressions for a probability law's truncated second moment.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

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

end ProbabilityTheory

end

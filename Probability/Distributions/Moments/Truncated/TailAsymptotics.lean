/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Power.TailIntegral
public import Analysis.Asymptotics.RegularVariation.Integral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Layercake
public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Moments.Truncated.Layercake

/-!
# Tail asymptotics for truncated second moments

This module converts asymptotics of the two-sided tail or its integrated form
into asymptotics of the truncated second moment.

## Public declarations

- If `u^(α-2) ∫₀^{u²} μ(x²>t) dt → A` and
  `u^α μ(|x|>u) → B`, then `u^(α-2) Vμ(u) → A-B`.
- If `u^α μ(|x|>u) → B>0` and `0<α<2`, then
  `u^(α-2) Vμ(u) → αB/(2-α)`.
- If `u ↦ μ(|x|>u)` is regularly varying with index `-α`, `0<α<2`, then
  `Vμ(u)/(u² μ(|x|>u)) → α/(2-α)`.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A finite limit for the normalized layer-cake integral and for
`u^α` times the two-sided tail gives the corresponding normalized truncated
second-moment limit. -/
theorem tendsto_truncatedSecondMoment_scale_of_layercake_and_tail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment μ u) atTop (nhds (A - B)) := by
  have hsub : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|}) atTop (nhds (A - B)) :=
    hA.sub hB
  have heq : (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment μ u) =ᶠ[atTop]
      fun u => u ^ (α - 2) * truncatedSquareTailIntegral μ u -
        u ^ α * μ.real {x : ℝ | u < |x|} := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [truncatedSecondMoment_eq_layercake_sub_tail μ hu.le,
      truncatedSquareTailIntegral]
    rw [mul_sub]
    have hpow : u ^ (α - 2) * u ^ 2 = u ^ α := by
      rw [← Real.rpow_natCast u 2, ← Real.rpow_add hu]
      congr 1
      ring
    rw [← mul_assoc, hpow]
  exact hsub.congr' heq.symm

/-- A two-sided power-tail asymptotic determines the normalized truncated
second-moment constant. If `u^α μ(|x| > u) → B` with `0 < α < 2`, then
`u^(α-2) ∫_{|x|≤u} x^2 μ(dx) → α B / (2-α)`. -/
theorem tendsto_truncatedSecondMoment_scale_of_twoSidedTail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α B : ℝ}
    (_hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * μ.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment μ u) atTop
      (nhds (α * B / (2 - α))) := by
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < x ^ 2}
  let β : ℝ := α / 2
  have hβ₁ : β < 1 := by dsimp [β]; linarith
  have hg_anti : Antitone g := by
    intro s t hst
    apply measureReal_mono (μ := μ) (s₁ := {x : ℝ | t < x ^ 2})
      (s₂ := {x : ℝ | s < x ^ 2}) (by
        intro x hx
        exact lt_of_le_of_lt hst hx) (by finiteness)
  have hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    exact measureReal_nonneg
  have hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1 := by
    intro t ht
    exact measureReal_le_one
  have hTailSqrt : Tendsto
      (fun t : ℝ => (Real.sqrt t) ^ α *
        μ.real {x : ℝ | Real.sqrt t < |x|}) atTop (nhds B) := by
    exact hTail.comp Real.tendsto_sqrt_atTop
  have hlimSquare : Tendsto (fun t : ℝ => t ^ β * g t) atTop (nhds B) := by
    apply hTailSqrt.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have hpow : t ^ β = (Real.sqrt t) ^ α := by
      dsimp [β]
      exact Real.rpow_div_two_eq_sqrt α ht.le
    have hset : {x : ℝ | t < x ^ 2} = {x : ℝ | Real.sqrt t < |x|} := by
      ext x
      constructor
      · intro hx
        apply (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).1
        simpa [Real.sq_sqrt ht.le] using hx
      · intro hx
        have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).2 hx
        simpa [Real.sq_sqrt ht.le] using hsq
    simp only [hpow, g, hset]
  have hKaramata :=
    _root_.Asymptotics.tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul
      (g := g) (β := β) (C := B) hβ₁ hB hg_anti hg_nonneg hg_le_one hlimSquare
  have hsquare : Tendsto
      (fun u : ℝ => (u ^ 2) ^ (β - 1) *
        ∫ t in (0:ℝ)..u ^ 2, g t) atTop (nhds (B / (1 - β))) := by
    apply hKaramata.comp
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max (1:ℝ) b)] with u hu
    have h1u : 1 ≤ u := le_trans (le_max_left 1 b) hu
    have hbu : b ≤ u := le_trans (le_max_right 1 b) hu
    have huu : u ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    exact hbu.trans huu
  have hmain : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral μ u)
      atTop (nhds (B / (1 - β))) := by
    apply hsquare.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    rw [truncatedSquareTailIntegral_eq_intervalIntegral μ hu.le]
    have hpow : (u ^ (2:ℕ)) ^ (β - 1) = u ^ (α - 2) := by
      rw [← Real.rpow_natCast u 2]
      calc
        (u ^ (2:ℝ)) ^ (β - 1) = u ^ ((2:ℝ) * (β - 1)) :=
          (Real.rpow_mul hu.le 2 (β - 1)).symm
        _ = u ^ (α - 2) := by
          congr 1
          dsimp [β]
          ring
    rw [hpow]
  have hmoment := tendsto_truncatedSecondMoment_scale_of_layercake_and_tail μ hmain hTail
  have hconst : B / (1 - β) - B = α * B / (2 - α) := by
    dsimp [β]
    field_simp [ne_of_gt (by linarith : 0 < (2:ℝ) - α)]
    ring
  rw [hconst] at hmoment
  exact hmoment

/-- Regular variation of the two-sided tail determines the truncated second
moment without requiring the slowly varying factor to converge. If
`T(u) = μ(|x| > u)` is regularly varying with index `-α`, where
`0 < α < 2`, then
`∫_{|x|≤u} x² μ(dx) / (u² T(u)) → α / (2-α)`. -/
theorem tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hTail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => μ.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun u : ℝ =>
      truncatedSecondMoment μ u /
        (u ^ 2 * μ.real {x : ℝ | u < |x|})) atTop
      (nhds (α / (2 - α))) := by
  let T : ℝ → ℝ := fun u => μ.real {x : ℝ | u < |x|}
  let g : ℝ → ℝ := fun t => μ.real {x : ℝ | t < x ^ 2}
  let β : ℝ := α / 2
  have hβ₀ : 0 < β := by dsimp [β]; linarith
  have hβ₁ : β < 1 := by dsimp [β]; linarith
  have hsetSqrt (t : ℝ) (ht : 0 ≤ t) :
      {x : ℝ | t < x ^ 2} = {x : ℝ | Real.sqrt t < |x|} := by
    ext x
    constructor
    · intro hx
      apply (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).1
      simpa [Real.sq_sqrt ht] using hx
    · intro hx
      have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg t) (abs_nonneg x)).2 hx
      simpa [Real.sq_sqrt ht] using hsq
  have hg_anti : Antitone g := by
    intro s t hst
    dsimp [g]
    apply measureReal_mono (μ := μ) (s₁ := {x : ℝ | t < x ^ 2})
      (s₂ := {x : ℝ | s < x ^ 2}) (by
        intro x hx
        exact lt_of_le_of_lt hst hx) (by finiteness)
  have hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t := by
    intro t ht
    exact measureReal_nonneg
  have hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1 := by
    intro t ht
    exact measureReal_le_one
  have hposT : ∀ᶠ u : ℝ in atTop, 0 < T u := by
    simpa [T] using hTail.eventually_pos
  have hposG : ∀ᶠ t : ℝ in atTop, 0 < g t := by
    have hsqrt := Real.tendsto_sqrt_atTop.eventually hposT
    filter_upwards [hsqrt, eventually_gt_atTop (0:ℝ)] with t htT ht
    rw [show g t = T (Real.sqrt t) by
      dsimp [g, T]
      rw [hsetSqrt t ht.le]]
    exact htT
  have hregG : Asymptotics.IsRegularlyVaryingAtTop g (-β) := by
    refine ⟨hposG, ?_⟩
    intro c hc
    let d : ℝ := Real.sqrt c
    have hd : 0 < d := Real.sqrt_pos.2 hc
    have hratioT := hTail.ratio_tendsto (c := d) hd
    have hratio := hratioT.comp Real.tendsto_sqrt_atTop
    have hratioEq : (fun t : ℝ => g (c * t) / g t) =ᶠ[atTop]
        fun t => T (d * Real.sqrt t) / T (Real.sqrt t) := by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
      have hct : 0 ≤ c * t := mul_nonneg hc.le ht.le
      have hgct : g (c * t) = T (Real.sqrt (c * t)) := by
        dsimp [g, T]
        rw [hsetSqrt (c * t) hct]
      have hgt : g t = T (Real.sqrt t) := by
        dsimp [g, T]
        rw [hsetSqrt t ht.le]
      rw [hgct, hgt, show Real.sqrt (c * t) = d * Real.sqrt t by
        dsimp [d]
        exact Real.sqrt_mul (le_of_lt hc) t]
    have hpow : d ^ (-α) = c ^ (-β) := by
      convert (Real.rpow_div_two_eq_sqrt (-α) hc.le).symm using 1
      · congr 1
        ring
    have hratio' : Tendsto
        (fun t : ℝ => T (d * Real.sqrt t) / T (Real.sqrt t)) atTop
        (nhds (c ^ (-β))) := by
      rw [← hpow]
      exact hratio
    exact hratio'.congr' hratioEq.symm
  have hKaramata := hregG.tendsto_intervalIntegral_div_mul_of_antitone
    (by linarith : 0 ≤ β) hβ₁ hg_anti hg_nonneg hg_le_one
  have hu2 : Tendsto (fun u : ℝ => u ^ 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with u hu
    have h1u : 1 ≤ u := le_trans (le_max_left 1 b) hu
    have hbu : b ≤ u := le_trans (le_max_right 1 b) hu
    have huu : u ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    exact hbu.trans huu
  have hscaled := hKaramata.comp hu2
  have hsetSquare (u : ℝ) (hu : 0 ≤ u) :
      {x : ℝ | u ^ 2 < x ^ 2} = {x : ℝ | u < |x|} := by
    ext x
    constructor
    · intro hx
      exact (sq_lt_sq₀ hu (abs_nonneg x)).1 (by simpa [sq_abs] using hx)
    · intro hx
      have hsq := (sq_lt_sq₀ hu (abs_nonneg x)).2 hx
      simpa [sq_abs] using hsq
  have hdenEq : (fun u : ℝ => u ^ 2 * g (u ^ 2)) =ᶠ[atTop]
      fun u => u ^ 2 * T u := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
    congr 1
    dsimp [g, T]
    rw [hsetSquare u hu]
  have hscale' : Tendsto (fun u : ℝ =>
      (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u)) atTop
      (nhds (1 / (1 - β))) := by
    have heq : (fun u : ℝ =>
        (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u)) =ᶠ[atTop]
        fun u => (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * g (u ^ 2)) := by
      filter_upwards [hdenEq] with u hu
      rw [hu]
    exact hscaled.congr' heq.symm
  have hlayer : Tendsto (fun u : ℝ =>
      truncatedSquareTailIntegral μ u / (u ^ 2 * T u)) atTop
      (nhds (1 / (1 - β))) := by
    have heq : (fun u : ℝ =>
        truncatedSquareTailIntegral μ u / (u ^ 2 * T u)) =ᶠ[atTop]
        fun u => (∫ t in (0:ℝ)..u ^ 2, g t) / (u ^ 2 * T u) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with u hu
      rw [truncatedSquareTailIntegral_eq_intervalIntegral μ hu]
    exact hscale'.congr' heq.symm
  have hsub : Tendsto (fun u : ℝ =>
      truncatedSquareTailIntegral μ u / (u ^ 2 * T u) - 1) atTop
      (nhds (1 / (1 - β) - 1)) := by
    simpa using hlayer.sub tendsto_const_nhds
  have hmomentEq : (fun u : ℝ =>
      truncatedSecondMoment μ u / (u ^ 2 * T u)) =ᶠ[atTop]
      fun u => truncatedSquareTailIntegral μ u / (u ^ 2 * T u) - 1 := by
    filter_upwards [eventually_gt_atTop (0:ℝ), hposT] with u hu hTu
    rw [truncatedSecondMoment_eq_layercake_sub_tail μ hu.le]
    dsimp [T]
    have hden : u ^ 2 * μ.real {x : ℝ | u < |x|} ≠ 0 :=
      ne_of_gt (mul_pos (sq_pos_of_pos hu) hTu)
    have htailNe : μ.real {x : ℝ | u < |x|} ≠ 0 := by
      simpa [T] using hTu.ne'
    field_simp [hden, htailNe]
  have hconst : 1 / (1 - β) - 1 = α / (2 - α) := by
    dsimp [β]
    field_simp [ne_of_gt (by linarith : 0 < 2 - α)]
    ring
  rw [hconst] at hsub
  exact hsub.congr' hmomentEq.symm

end ProbabilityTheory

end

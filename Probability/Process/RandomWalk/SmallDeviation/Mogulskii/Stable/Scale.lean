/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic

/-!
# Stable small-deviation block lengths

Write $b_n$ for `stableBlockLength α ν constant scale n`, $T_n$ for
`stableScaleTime α ν (scale n)`, and $r_n$ for the stable rate.
The public declarations are:

- `stableBlockArgument` and `stableBlockLength`:
  $B_n=\operatorname{constant}\,T_n$ and $b_n=\lfloor B_n\rfloor_+$.
- `tendsto_stableBlockArgument_atTop`,
  `tendsto_stableBlockLength_atTop`, and
  `eventually_stableBlockLength_pos`:
  $B_n,b_n\to\infty$, hence eventually $b_n>0$.
- `tendsto_stableBlockArgument_floor_div` and
  `tendsto_stableBlockLength_div_stableScaleTime`:
  $b_n/B_n\to1$ and $b_n/T_n\to\operatorname{constant}$.
- `tendsto_stableBlockNorming_div_scale_of_slowVariation_limit`:
  the stable norming at time $b_n$ divided by the corridor width tends
  to $\operatorname{constant}^{1/\alpha}$ when $L_\alpha^*$ has a positive limit.
- `stableBlockArgument_eq_mul_stableSmallDeviationRate`,
  `stableBlockArgument_eq_constant_mul_stableScaleTime`, and
  `tendsto_stableBlockLength_div_nat_zero`:
  $B_n=\operatorname{constant}\,n r_n$ and $b_n/n\to0$.
- `tendsto_stableBlockLength_atTop_of_slowVariation`,
  `eventually_stableBlockLength_pos_of_slowVariation`,
  `tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation`, and
  `tendsto_stableBlockLength_div_nat_zero_of_slowVariation`:
  the same growth, positivity, ratio, and negligible-horizon conclusions
  under slow variation without a positive-limit assumption.

These block scales are those used in Mogul'skii, *Small Deviations in a
Space of Trajectories*, Theorem 3, Section 4.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory
open Asymptotics

/-! ## Stable block lengths -/

/-- The unrounded number of steps in a stable small-deviation block. The spatial corridor scale is
`scale n`; by the inverse norming relation, a walk travels this distance in `B* (scale n) =
scale n ^ α / L* (scale n)` steps, up to the multiplicative block parameter `constant`. The separate stable
normalization `b n` is used to compare this block length with the full horizon `n`. -/
noncomputable def stableBlockArgument
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  constant * scale n ^ α / stableSlowVariation α ν (scale n)

/-- The number of steps of one block of the stable partition, the floor of `stableBlockArgument`. -/
noncomputable def stableBlockLength
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊stableBlockArgument α ν constant scale n⌋₊

/-- If the slowly varying factor of (3) stays in a positive interval along the block scale, then the
unrounded block length tends to infinity along it. -/
theorem tendsto_stableBlockArgument_atTop
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (stableBlockArgument α ν constant scale) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have hlow : ∀ᶠ n in atTop, b ≤ (constant / K) * scale n ^ α :=
    ((tendsto_rpow_atTop hα).comp hscale |>.const_mul_atTop (div_pos hconstant hK)).eventually
      (eventually_ge_atTop b)
  filter_upwards [hlow, hvariation, hscale.eventually (eventually_gt_atTop 0)] with n hb hn hsn
  have hpow : 0 < scale n ^ α := Real.rpow_pos_of_pos hsn _
  have hstep : (constant / K) * scale n ^ α ≤
      constant * scale n ^ α / stableSlowVariation α ν (scale n) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (le_of_lt (mul_pos hconstant hpow)) hn.1 hn.2
  rw [stableBlockArgument]
  linarith

/-- The block length tends to infinity along the block scale. -/
theorem tendsto_stableBlockLength_atTop
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (stableBlockLength α ν constant scale) atTop atTop := by
  change Tendsto (floorBlockLength (stableBlockArgument α ν constant scale))
    atTop atTop
  exact tendsto_floorBlockLength_atTop
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- The block length is eventually positive along the block scale. -/
theorem eventually_stableBlockLength_pos
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α ν constant scale n := by
  change ∀ᶠ n in atTop,
    0 < floorBlockLength (stableBlockArgument α ν constant scale) n
  exact eventually_floorBlockLength_pos
    (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation)

/-- Rounding the block length down does not change its ratio to the unrounded block length. -/
theorem tendsto_stableBlockArgument_floor_div
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n) atTop (nhds 1) := by
  simpa [floorBlockLength] using
    (tendsto_floorBlockLength_div_argument
      (tendsto_stableBlockArgument_atTop hα hconstant hK hscale hvariation))

/-- The rounded stable block length is asymptotic to the stable time scale
times its fixed block parameter.  This is the rounding relation for
`mₙ = ⌊constant · B*(aₙ)⌋₊`; it does not yet identify the norming at `mₙ` with
`aₙ`, which requires regular variation of the inverse norming. -/
theorem tendsto_stableBlockLength_div_stableScaleTime
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) atTop (nhds constant) := by
  have hfloor := tendsto_stableBlockArgument_floor_div
    hα hconstant hK hscale hvariation
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hvariation]
      with n hscalePos hvar
    exact div_pos (Real.rpow_pos_of_pos hscalePos α) hvar.1
  have hargRatio : Tendsto
      (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) atTop (nhds constant) := by
    have hargEq (n : ℕ) : stableBlockArgument α ν constant scale n =
        constant * stableScaleTime α ν (scale n) := by
      rw [stableBlockArgument, stableScaleTime]
      ring
    have heq : (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) =ᶠ[atTop] fun _ => constant := by
      filter_upwards [hscaleTimePos] with n htime
      rw [hargEq n]
      field_simp [htime.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hmul : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
        (stableBlockArgument α ν constant scale n /
          stableScaleTime α ν (scale n))) atTop (nhds (1 * constant)) := by
    simpa [stableBlockLength, floorBlockLength] using hfloor.mul hargRatio
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) =ᶠ[atTop]
      fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
        (stableBlockArgument α ν constant scale n /
          stableScaleTime α ν (scale n)) := by
    filter_upwards [hscaleTimePos,
      eventually_stableBlockLength_pos hα hconstant hK hscale hvariation]
      with n htime hlen
    have hargEq : stableBlockArgument α ν constant scale n =
        constant * stableScaleTime α ν (scale n) := by
      rw [stableBlockArgument, stableScaleTime]
      ring
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [hargEq]
      exact mul_pos hconstant htime
    field_simp [htime.ne', hargPos.ne']
  simpa using hmul.congr' heq.symm

/-- If the slowly varying factor has a positive finite limit, the norming at a
rounded stable block length has the expected spatial scale.  This is the
normalization bridge needed by the domain-of-attraction block endpoint
theorem.  The hypothesis on the limit is kept explicit here; proving it for
the stable limit law is a separate distributional tail theorem. -/
theorem tendsto_stableBlockNorming_div_scale_of_slowVariation_limit
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {constant ell : ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hell : 0 < ell)
    (hscale : Tendsto scale atTop atTop)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell))
    (hnorm : IsStableNorming α ν normalization) :
    Tendsto (fun n => normalization (stableBlockLength α ν constant scale n) /
      scale n) atTop (nhds (constant ^ (1 / α))) := by
  let block : ℕ → ℕ := stableBlockLength α ν constant scale
  have hslowWindow : ∀ᶠ u in atTop,
      0 < stableSlowVariation α ν u ∧ stableSlowVariation α ν u ≤ ell + 1 := by
    have hmem : Set.Ioo (ell / 2) (ell + 1) ∈ 𝓝 ell := by
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [hslow.eventually hmem]
      with u hu
    exact ⟨by linarith, by linarith⟩
  have hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧
        stableSlowVariation α ν (scale n) ≤ ell + 1 :=
    hscale.eventually hslowWindow
  have hblockTop : Tendsto block atTop atTop := by
    simpa [block] using tendsto_stableBlockLength_atTop
      hα hconstant (by linarith : 0 < ell + 1) hscale hvariation
  have hblockScale : Tendsto
      (fun n => (block n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds constant) := by
    simpa [block] using tendsto_stableBlockLength_div_stableScaleTime
      hα hconstant (by linarith : 0 < ell + 1) hscale hvariation
  have hslowScale : Tendsto (fun n => stableSlowVariation α ν (scale n))
      atTop (nhds ell) := hslow.comp hscale
  have hslowBlock : Tendsto
      (fun n => stableSlowVariation α ν (normalization (block n)))
      atTop (nhds ell) := by
    exact hslow.comp (hnorm.2.1.comp hblockTop)
  have hnormRatioBlock : Tendsto
      (fun n => normalization (block n) ^ α /
        stableSlowVariation α ν (normalization (block n)) / (block n : ℝ))
      atTop (nhds 1) := hnorm.2.2.comp hblockTop
  have hnormPowerBlock : Tendsto
      (fun n => normalization (block n) ^ α / (block n : ℝ))
      atTop (nhds ell) := by
    have hmul := hnormRatioBlock.mul hslowBlock
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (normalization (block n)) := by
      filter_upwards [hslowBlock.eventually (Ioi_mem_nhds hell)] with n hn
      exact hn
    have heq : (fun n => normalization (block n) ^ α /
        stableSlowVariation α ν (normalization (block n)) / (block n : ℝ) *
          stableSlowVariation α ν (normalization (block n))) =ᶠ[atTop]
        fun n => normalization (block n) ^ α / (block n : ℝ) := by
      filter_upwards [hblockPos, hslowPos] with n hn hL
      field_simp [show (block n : ℝ) ≠ 0 by exact_mod_cast hn.ne', hL.ne']
    simpa only [one_mul] using hmul.congr' heq
  have hblockOverScalePow : Tendsto
      (fun n => (block n : ℝ) / scale n ^ α) atTop
      (nhds (constant / ell)) := by
    have hdiv := hblockScale.div hslowScale hell.ne'
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    have hslowPos : ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) := by
      filter_upwards [hslowScale.eventually (Ioi_mem_nhds hell)] with n hn
      exact hn
    have heq : (fun n => (block n : ℝ) / stableScaleTime α ν (scale n) /
        stableSlowVariation α ν (scale n)) =ᶠ[atTop]
        fun n => (block n : ℝ) / scale n ^ α := by
      filter_upwards [hscalePos, hslowPos] with n hx hL
      rw [stableScaleTime]
      field_simp [hL.ne', (Real.rpow_pos_of_pos hx α).ne']
    exact hdiv.congr' heq
  have hratioPower : Tendsto
      (fun n => (normalization (block n) / scale n) ^ α) atTop
        (nhds constant) := by
    have hmul := hnormPowerBlock.mul hblockOverScalePow
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    have hnormPos : ∀ᶠ n in atTop, 0 < normalization (block n) := by
      filter_upwards [hblockPos] with n hn
      exact hnorm.1 (block n) hn
    have heq : (fun n => normalization (block n) ^ α / (block n : ℝ) *
        ((block n : ℝ) / scale n ^ α)) =ᶠ[atTop]
        fun n => (normalization (block n) / scale n) ^ α := by
      filter_upwards [hblockPos, hscalePos, hnormPos] with n hm hx hb
      rw [Real.div_rpow (le_of_lt hb) (le_of_lt hx)]
      have hmne : (block n : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hxpowne : scale n ^ α ≠ 0 := (Real.rpow_pos_of_pos hx α).ne'
      field_simp [hmne, hxpowne]
    have hlim : ell * (constant / ell) = constant := by
      field_simp [hell.ne']
    simpa only [hlim] using hmul.congr' heq
  have hroot : Tendsto
      (fun n => ((normalization (block n) / scale n) ^ α) ^ (1 / α))
      atTop (nhds (constant ^ (1 / α))) :=
    hratioPower.rpow_const (Or.inl hconstant.ne')
  have hratioPos : ∀ᶠ n in atTop,
      0 < normalization (block n) / scale n := by
    have hblockPos : ∀ᶠ n in atTop, 0 < block n :=
      hblockTop.eventually (eventually_gt_atTop 0)
    have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
      hscale.eventually (eventually_gt_atTop 0)
    filter_upwards [hblockPos, hscalePos] with n hm hx
    exact div_pos (hnorm.1 (block n) hm) hx
  have heq : (fun n => ((normalization (block n) / scale n) ^ α) ^ (1 / α)) =ᶠ[atTop]
      fun n => normalization (block n) / scale n := by
    filter_upwards [hratioPos] with n hn
    rw [← Real.rpow_mul (le_of_lt hn) α (1 / α)]
    rw [show α * (1 / α) = 1 by field_simp]
    exact Real.rpow_one _
  simpa using hroot.congr' heq

/-- The unrounded stable block length is `constant * n` times the small-deviation rate evaluated at the
corridor scale. -/
theorem stableBlockArgument_eq_mul_stableSmallDeviationRate
    {α : ℝ} {ν : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hn : (n : ℝ) ≠ 0) (hL : stableSlowVariation α ν (scale n) ≠ 0) :
    stableBlockArgument α ν constant scale n =
      constant * n * stableSmallDeviationRate α ν scale n := by
  have hden : (n : ℝ) * stableSlowVariation α ν (scale n) ≠ 0 := mul_ne_zero hn hL
  rw [stableBlockArgument, stableSmallDeviationRate]
  field_simp

/-- If the stable small-deviation rate tends to zero, one block occupies a vanishing fraction of the full
horizon. The hypotheses ensure the floor asymptotic and identify the unrounded block length with
`constant * n * stableSmallDeviationRate`. -/
theorem tendsto_stableBlockLength_div_nat_zero
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) / n)
      atTop (nhds 0) := by
  have hfloor := tendsto_stableBlockArgument_floor_div hα hconstant hK hscale hvariation
  have hrateMul : Tendsto (fun n => constant * stableSmallDeviationRate α ν scale n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hargDiv : Tendsto (fun n => stableBlockArgument α ν constant scale n / n)
      atTop (nhds 0) := by
    have heq : (fun n => stableBlockArgument α ν constant scale n / n) =ᶠ[atTop]
        fun n => constant * stableSmallDeviationRate α ν scale n := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation] with n hn hvar
      rw [stableBlockArgument_eq_mul_stableSmallDeviationRate]
      · field_simp
      · exact_mod_cast hn.ne'
      · exact hvar.1.ne'
    exact hrateMul.congr' heq.symm
  have hmul : Tendsto
      (fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / n))
      atTop (nhds 0) := by
    simpa using hfloor.mul hargDiv
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) / n) =ᶠ[atTop]
      fun n => (⌊stableBlockArgument α ν constant scale n⌋₊ : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / n) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hvariation,
      hscale.eventually (eventually_gt_atTop 0)] with n hn hvar hscalePos
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [stableBlockArgument]
      exact div_pos (mul_pos hconstant (Real.rpow_pos_of_pos hscalePos α)) hvar.1
    simp only [stableBlockLength]
    field_simp [hargPos.ne', Nat.cast_ne_zero.mpr hn.ne']
  exact hmul.congr' heq.symm


/-! ## Block-scale estimates without boundedness of the slow factor -/

/-- The real block argument is the stable time scale multiplied by the block
parameter. -/
theorem stableBlockArgument_eq_constant_mul_stableScaleTime
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockArgument α ν constant scale n =
      constant * stableScaleTime α ν (scale n) := by
  rw [stableBlockArgument, stableScaleTime]
  ring

/-- Under slow variation, a stable block length tends to infinity without a
boundedness assumption on the slowly varying factor. -/
theorem tendsto_stableBlockLength_atTop_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hconstant : 0 < constant) (hscale : Tendsto scale atTop atTop) :
    Tendsto (stableBlockLength α ν constant scale) atTop atTop := by
  have hκ : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow
  have hκscale : Tendsto (fun n => stableScaleTime α ν (scale n)) atTop atTop :=
    hκ.comp hscale
  have harg : Tendsto (stableBlockArgument α ν constant scale) atTop atTop := by
    have hmul : Tendsto (fun n => constant * stableScaleTime α ν (scale n))
        atTop atTop := hκscale.const_mul_atTop hconstant
    convert hmul using 1
    funext n
    exact stableBlockArgument_eq_constant_mul_stableScaleTime α ν constant scale n
  change Tendsto (Asymptotics.floorBlockLength
    (stableBlockArgument α ν constant scale)) atTop atTop
  exact Asymptotics.tendsto_floorBlockLength_atTop harg

/-- The rounded stable block length is eventually positive under slow
variation, even when the slowly varying factor diverges. -/
theorem eventually_stableBlockLength_pos_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hconstant : 0 < constant) (hscale : Tendsto scale atTop atTop) :
    ∀ᶠ n in atTop, 0 < stableBlockLength α ν constant scale n := by
  exact (tendsto_stableBlockLength_atTop_of_slowVariation
    hα hα₂ hslow hconstant hscale).eventually (eventually_gt_atTop 0)

/-- The rounded block length is asymptotic to the stable time scale times
the fixed block parameter under slow variation. -/
theorem tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hconstant : 0 < constant) (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) atTop (nhds constant) := by
  have hκ : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow
  have hκscale : Tendsto (fun n => stableScaleTime α ν (scale n)) atTop atTop :=
    hκ.comp hscale
  have hκpos : ∀ᶠ n in atTop, 0 < stableScaleTime α ν (scale n) :=
    hκscale.eventually (eventually_gt_atTop 0)
  have harg : Tendsto (stableBlockArgument α ν constant scale) atTop atTop := by
    have hmul := hκscale.const_mul_atTop hconstant
    convert hmul using 1
    funext n
    exact stableBlockArgument_eq_constant_mul_stableScaleTime α ν constant scale n
  have hfloor : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n)
      atTop (nhds 1) := by
    simpa [stableBlockLength, Asymptotics.floorBlockLength] using
      Asymptotics.tendsto_floorBlockLength_div_argument harg
  have hargRatio : Tendsto
      (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) atTop (nhds constant) := by
    have heq : (fun n => stableBlockArgument α ν constant scale n /
        stableScaleTime α ν (scale n)) =ᶠ[atTop] fun _ => constant := by
      filter_upwards [hκpos] with n hpos
      rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
      field_simp [hpos.ne']
    exact tendsto_const_nhds.congr' heq.symm
  have hmul : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n /
            stableScaleTime α ν (scale n)))
      atTop (nhds (1 * constant)) := hfloor.mul hargRatio
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) /
      stableScaleTime α ν (scale n)) =ᶠ[atTop]
      fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n /
            stableScaleTime α ν (scale n)) := by
    filter_upwards [hκpos] with n hκn
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
      exact mul_pos hconstant hκn
    field_simp [hκn.ne', hargPos.ne']
  simpa using hmul.congr' heq.symm

/-- A stable block occupies a vanishing fraction of the full horizon when
the small-deviation rate tends to zero. Slow variation suffices; no upper
bound on its values along the scale is needed. -/
theorem tendsto_stableBlockLength_div_nat_zero_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {constant : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hconstant : 0 < constant) (hscale : Tendsto scale atTop atTop)
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) / n)
      atTop (nhds 0) := by
  have hκ : Tendsto (stableScaleTime α ν) atTop atTop :=
    stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow
  have hκscale := hκ.comp hscale
  have hκpos : ∀ᶠ n in atTop, 0 < stableScaleTime α ν (scale n) :=
    hκscale.eventually (eventually_gt_atTop 0)
  have harg : Tendsto (stableBlockArgument α ν constant scale) atTop atTop := by
    have hmul := hκscale.const_mul_atTop hconstant
    convert hmul using 1
    funext n
    exact stableBlockArgument_eq_constant_mul_stableScaleTime α ν constant scale n
  have hfloor : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n)
      atTop (nhds 1) := by
    simpa [stableBlockLength, Asymptotics.floorBlockLength] using
      Asymptotics.tendsto_floorBlockLength_div_argument harg
  have hrateMul : Tendsto (fun n => constant * stableSmallDeviationRate α ν scale n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hargDiv : Tendsto
      (fun n => stableBlockArgument α ν constant scale n / (n : ℝ))
      atTop (nhds 0) := by
    have hslowPos : ∀ᶠ n in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscale.eventually hslow.eventually_pos
    have heq : (fun n => stableBlockArgument α ν constant scale n / (n : ℝ)) =ᶠ[atTop]
        fun n => constant * stableSmallDeviationRate α ν scale n := by
      filter_upwards [eventually_gt_atTop (0 : ℕ), hslowPos] with n hn hL
      rw [stableBlockArgument_eq_mul_stableSmallDeviationRate
        (by exact_mod_cast hn.ne') hL.ne']
      field_simp
    exact hrateMul.congr' heq.symm
  have hmul : Tendsto
      (fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / (n : ℝ)))
      atTop (nhds 0) := by
    simpa using hfloor.mul hargDiv
  have heq : (fun n => (stableBlockLength α ν constant scale n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      fun n => (stableBlockLength α ν constant scale n : ℝ) /
        stableBlockArgument α ν constant scale n *
          (stableBlockArgument α ν constant scale n / (n : ℝ)) := by
    filter_upwards [hκpos, eventually_gt_atTop (0 : ℕ)] with n hκn hn
    have hargPos : 0 < stableBlockArgument α ν constant scale n := by
      rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
      exact mul_pos hconstant hκn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp [hargPos.ne', hnPos.ne']
  exact hmul.congr' heq.symm

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

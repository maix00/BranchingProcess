/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
public import Probability.Distributions.Stable.Attraction.Norming.Basic

import Analysis.Asymptotics.Scale.Block.Count

/-!
# Stable-scale block-count asymptotics

Let $T_n=T_\alpha(a_n)$ be the stable time scale,
$b_n=\lfloor cT_n\rfloor$ the stable block length, and
$r_n=T_n/n$ the small-deviation rate.

## Public declarations

This module defines the complete-block count and records its asymptotics:

- `stableBlockCount`: the natural-number quotient of the horizon by the
  stable block length.
- `tendsto_stableScaleTime_div_nat_mul_stableBlockCount`:
  $T_n\lfloor n/b_n\rfloor/n\to1/c$, assuming the stable factor is eventually
  bounded above and below by positive constants and $r_n\to0$.
- `tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit`:
  the same limit when the stable factor tends to a positive finite limit.
- `tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation`:
  the same limit under slow variation and the two-scale condition.
- `tendsto_stableScaleTime_div_nat_mul_segmentBlockCount`:
  if $h_n/n\to\tau$, then
  $r_n\lfloor h_n/b_n\rfloor\to\tau/c$.

These are the stable-scale specializations of the generic quotient and
remainder estimates in `Analysis/Asymptotics/Scale/Block/Count.lean`. They
support the block partitions in A. A. Mogul'skii, *Small Deviations in a Space
of Trajectories*, Theorem 3, Section 4. The endpoint-core estimate that
reserves one additional bridge block remains theorem-specific under
`Stable/Discrete/Lemmas/Partition/BalancedCoreCount.lean`.

The original article is A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The number of complete stable blocks of length `stableBlockLength` that
fit in a horizon of `n` steps. -/
noncomputable def stableBlockCount (α : ℝ) (ν : Measure ℝ) (constant : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  n / stableBlockLength α ν constant scale n

/-- The stable time scale divided by the horizon, multiplied by the number
of complete stable blocks, tends to the reciprocal block parameter. The
assumptions allow the slowly varying factor to vary, provided it stays
eventually positive and bounded above and the small-deviation rate vanishes.
-/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) atTop (nhds constant⁻¹) := by
  have hlengthPos := eventually_stableBlockLength_pos
    hα hconstant hK hscale hvariation
  have hlengthRate := tendsto_stableBlockLength_div_nat_zero
    hα hconstant hK hscale hvariation hrate
  have hhorizon : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_self (by exact_mod_cast hn.ne')
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).congr' heq.symm
  have hlengthScale := tendsto_stableBlockLength_div_stableScaleTime
    hα hconstant hK hscale hvariation
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hvariation]
      with n hscalePos hvar
    exact div_pos (Real.rpow_pos_of_pos hscalePos α) hvar.1
  have hinverse := hlengthScale.inv₀ hconstant.ne'
  have hscaleOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
    apply hinverse.congr'
    filter_upwards [hscaleTimePos, hlengthPos] with n htime hlength
    have htimeNe : stableScaleTime α ν (scale n) ≠ 0 := htime.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [htimeNe, hlengthNe]
  simpa [stableBlockCount] using
    Asymptotics.tendsto_div_nat_mul_quotientBlockCount
      (horizon := fun n : ℕ => n) hhorizon hlengthPos hlengthRate hscaleOverLength

/-- The block-count scale relation follows from the two-scale hypothesis in
Mogul'skii, *Small Deviations in a Space of Trajectories*, Theorem 3,
Section 4, once `L*` is known to converge to a positive finite limit. This
packages the rate and boundedness consequences without adding them as separate
assumptions. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
    {α ell : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {constant : ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) atTop (nhds constant⁻¹) := by
  have hwindow : ∀ᶠ u in atTop,
      0 < stableSlowVariation α ν u ∧ stableSlowVariation α ν u ≤ ell + 1 := by
    have hmem : Set.Ioo (ell / 2) (ell + 1) ∈ nhds ell := by
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [hslow.eventually hmem]
      with u hu
    exact ⟨by linarith, by linarith⟩
  have hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧
        stableSlowVariation α ν (scale n) ≤ ell + 1 :=
    (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.scale_tendsto_atTop hscale).eventually hwindow
  have hrate := IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    hα hell hscale hslow
  exact tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    hα hconstant (by linarith : 0 < ell + 1)
    (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.scale_tendsto_atTop hscale) hvariation hrate

/-- The stable block count has the expected asymptotic under slow variation
alone. In particular, no boundedness assumption is imposed on `L*` along the
small-deviation scale. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hconstant : 0 < constant)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
  have hscaleTop := hscale.scale_tendsto_atTop
  have hlengthPos := eventually_stableBlockLength_pos_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop
  have hlengthRate := tendsto_stableBlockLength_div_nat_zero_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop hrate
  have hhorizon : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_self (by exact_mod_cast hn.ne')
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).congr' heq.symm
  have hlengthScale := tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    have htop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
      hα hα₂ hslow
    exact (htop.comp hscaleTop).eventually (eventually_gt_atTop 0)
  have hinverse := hlengthScale.inv₀ hconstant.ne'
  have hscaleOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
    apply hinverse.congr'
    filter_upwards [hscaleTimePos, hlengthPos] with n htime hlength
    have htimeNe : stableScaleTime α ν (scale n) ≠ 0 := htime.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [htimeNe, hlengthNe]
  simpa [stableBlockCount] using
    Asymptotics.tendsto_div_nat_mul_quotientBlockCount
      (horizon := fun n : ℕ => n) hhorizon hlengthPos hlengthRate hscaleOverLength

/-- A fixed macroscopic subinterval of relative length `τ` contains the
asymptotic cost `τ / constant` in stable blocks. The block length is chosen
from the common small-deviation scale at the full horizon; only the horizon
of the subinterval varies. This is the block-count input for each cell of a
finite step-corridor partition. -/
theorem tendsto_stableScaleTime_div_nat_mul_segmentBlockCount
    {α τ : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    {horizon : ℕ → ℕ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hconstant : 0 < constant)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / n)
      atTop (nhds τ)) :
    Tendsto (fun n => stableSmallDeviationRate α ν scale n *
      ((horizon n / stableBlockLength α ν constant scale n : ℕ) : ℝ))
      atTop (nhds (τ / constant)) := by
  let blockLength : ℕ → ℕ := stableBlockLength α ν constant scale
  have hscaleTop := hscale.scale_tendsto_atTop
  have hrate := tendsto_stableSmallDeviationRate_zero_of_slowVariation
    hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
    hα hα₂ hslow
  have hblockPos : ∀ᶠ n in atTop, 0 < blockLength n := by
    simpa [blockLength] using eventually_stableBlockLength_pos_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hblockOverN : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0) := by
    simpa [blockLength] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop hrate
  have hlengthScale : Tendsto (fun n => (blockLength n : ℝ) /
      stableScaleTime α ν (scale n)) atTop (nhds constant) := by
    simpa [blockLength] using tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hκPos : ∀ᶠ n in atTop, 0 < stableScaleTime α ν (scale n) := by
    have hκTop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
      hα hα₂ hslow
    exact (hκTop.comp hscaleTop).eventually (eventually_gt_atTop 0)
  have hκOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) / (blockLength n : ℝ))
      atTop (nhds constant⁻¹) := by
    have hinv := hlengthScale.inv₀ hconstant.ne'
    apply hinv.congr'
    filter_upwards [hκPos, hblockPos] with n hκ hlength
    have hκne : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
    have hlengthNe : (blockLength n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [hκne, hlengthNe]
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hslowPos : ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hslowPos] with n hn hL
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [stableSmallDeviationRate, stableScaleTime]
    field_simp [hnNe, hL.ne']
  have hscaledCount := Asymptotics.tendsto_div_nat_mul_quotientBlockCount
    hhorizon hblockPos hblockOverN hκOverLength
  have heq : (fun n => stableSmallDeviationRate α ν scale n *
      ((horizon n / blockLength n : ℕ) : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
        ((horizon n / blockLength n : ℕ) : ℝ) := by
    filter_upwards [hrateEq] with n hrateN
    rw [hrateN]
  have hlimit := hscaledCount.congr' heq.symm
  convert hlimit using 1
  field_simp [hconstant.ne']

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.SlowScale
public import Analysis.Asymptotics.Scale.Block.Length
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Inverse

/-!
# Stable-scale multiplier selection

These public constructions specialize the generic regular-variation diagonal
theorems in `Analysis.Asymptotics.RegularVariation.SlowScale` to the stable
time function. For a stable
small-deviation scale $a_n=o(b_n)$, they choose a diverging multiplier whose
product with $a_n/b_n$ still tends to zero, while retaining the corresponding
regular-variation limit for the stable time scale. The second lemma also
retains a family of fixed-parameter eventual conditions.

## Public declarations

- `IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier`:
  there is a nondecreasing $d_n\to\infty$ such that
  $d_na_n/b_n\to0$ and
  $T_\alpha(d_na_n)/(d_n^\alpha T_\alpha(a_n))\to1$, where
  $T_\alpha(u)=\mathrm{stableScaleTime}(\alpha,\nu,u)$.
- `IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_floor_scaleTime_ratio`:
  under $0<\alpha\le2$ and finite $\nu$, the multiplier can be chosen so
  $\lfloor T_\alpha(d_na_n)\rfloor/(d_n^\alpha T_\alpha(a_n))\to1$;
  this is the rounded scale relation in Mogul'skii's Theorem 4, equation
  (43).
- `IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier_of_eventually`:
  the same limits hold for a natural-valued $d_n$ while any family of
  fixed-parameter conditions $P(k,n)$ remains true at $k=d_n+1$ eventually.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

namespace IsStableMogulskiiScale

/-- Specialize the generic slowly varying diagonal to the stable time scale. -/
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

/-- Choose a slowly growing multiplier for which the rounded stable time
scale has the ratio used in equation (43) of Theorem 4, Section 5, of
A. A. Mogul'skii, *Small Deviations in the Sample Function Space*,
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, *Small Deviations in a Space of Trajectories*,
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081:
\[
  \frac{\lfloor T_\alpha(a_n x_n)\rfloor}
       {a_n^\alpha T_\alpha(x_n)} \longrightarrow 1.
\]
The same choice keeps $a_n x_n/b_n\to0$, where $b_n$ is the stable
normalization and $x_n$ is the smaller path scale. The floor factor follows
from divergence of $T_\alpha(a_nx_n)$ and the generic regular-variation
diagonal already used by
`exists_tendsto_slowStableScaleTime_multiplier`. -/
theorem exists_tendsto_slowStableScaleTime_floor_scaleTime_ratio
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hα₀ : 0 < α) (hα_le_two : α ≤ 2) :
    ∃ a : ℕ → ℝ, Monotone a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a n * (scale n / normalization n)) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (Asymptotics.floorBlockLength
          (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ) /
          (a n ^ α * stableScaleTime α ν (scale n))) atTop (nhds 1) := by
  obtain ⟨a, haMono, haTop, hsmall, hratio⟩ :=
    hscale.exists_tendsto_slowStableScaleTime_multiplier hslow
  let argument : ℕ → ℝ := fun n => stableScaleTime α ν (a n * scale n)
  have hax : Tendsto (fun n => a n * scale n) atTop atTop :=
    haTop.atTop_mul_atTop₀ hscale.scale_tendsto_atTop
  have hκtop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
    hα₀ hα_le_two hslow
  have hargument : Tendsto argument atTop atTop := by
    exact hκtop.comp (by simpa [argument] using hax)
  have hfloor := Asymptotics.tendsto_floorBlockLength_div_argument
    (argument := argument) hargument
  have hκscale : Tendsto (fun n => stableScaleTime α ν (scale n))
      atTop atTop := hκtop.comp hscale.scale_tendsto_atTop
  have hargumentPos : ∀ᶠ n : ℕ in atTop, 0 < argument n :=
    hargument.eventually_gt_atTop 0
  have hκscalePos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (scale n) := hκscale.eventually_gt_atTop 0
  have haPos : ∀ᶠ n : ℕ in atTop, 0 < a n :=
    haTop.eventually_gt_atTop 0
  have haPowPos : ∀ᶠ n : ℕ in atTop, 0 < a n ^ α := by
    filter_upwards [haPos] with n han
    exact Real.rpow_pos_of_pos han α
  have hproduct := hfloor.mul hratio
  have heq : (fun n =>
      (Asymptotics.floorBlockLength argument n : ℝ) /
        (a n ^ α * stableScaleTime α ν (scale n))) =ᶠ[atTop]
      fun n =>
        ((Asymptotics.floorBlockLength argument n : ℝ) / argument n) *
          ((stableScaleTime α ν (a n * scale n) /
            stableScaleTime α ν (scale n)) / a n ^ α) := by
    filter_upwards [hargumentPos, hκscalePos, haPowPos] with n hnArg hnScale hnPow
    dsimp [argument]
    field_simp [hnArg.ne', hnScale.ne', hnPow.ne']
    rw [mul_div_cancel_right₀ _ hnArg.ne']
  refine ⟨a, haMono, haTop, hsmall, ?_⟩
  simpa only [one_mul] using hproduct.congr' heq.symm

/-- Choose one natural-valued diagonal that also preserves fixed-parameter
eventual conditions. -/
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

end IsStableMogulskiiScale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

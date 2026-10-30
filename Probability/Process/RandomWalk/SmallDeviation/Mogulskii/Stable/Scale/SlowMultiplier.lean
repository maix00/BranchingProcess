/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation.SlowScale
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

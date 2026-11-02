/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Scale.Block.Partition
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
import Probability.Distributions.Stable.Attraction.Norming.Basic

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate

/-!
# Balanced block limits for the stable endpoint argument

This file contains a proof-chain lemma for the stable endpoint-cell lower
bound. If the horizon satisfies $H_n/n\to d>0$, the stable reference length
$r_n\to\infty$, $r_n/n\to0$, and $r_n/T_n\to a$ for an eventually positive
clock $T_n$, then the balanced block count tends to infinity, both possible
block lengths tend to infinity, and their ratios to $T_n$ tend to $a$.

The general partition theorem, independent of stable probability theory, is
`Asymptotics.tendsto_balancedBlockPartition_of_vanishingReference`.

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.balancedStableCellBlock_asymptotics`:
  for $0<\alpha\leq2$, $a>0$, a stable Mogulskii scale with slowly varying
  factor, and a cell horizon $H_n/n\to d>0$, the balanced block count and
  both possible block lengths tend to infinity. Put
$r_n=\mathrm{stableBlockLength}(\alpha,\nu,a^\alpha,\mathrm{scale},n)$,
$T_n=\mathrm{stableScaleTime}(\alpha,\nu,\mathrm{scale}(n))$, and
$\ell_n=\mathrm{balancedBlockShortLength}(H_n,r_n)$. The limits are

$$
\frac{\ell_n}{T_n}\to a^\alpha,
\qquad \frac{\ell_n+1}{T_n}\to a^\alpha.
$$

It is kept under `Lemmas/` because it is used only in this proof chain for
the stable finite-partition construction in A. A. Mogul'skii, Theorem 3,
Section 4, p. 764, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open scoped Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- In a macroscopic partition cell, both balanced block lengths are
asymptotic to the stable reference length, in the stable clock. This
specializes the general vanishing-reference partition theorem to the stable
Mogulskii scale. -/
lemma balancedStableCellBlock_asymptotics
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (total : ℕ → ℕ) {duration amplitude : ℝ}
    (hduration : 0 < duration) (hamplitude : 0 < amplitude)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    Tendsto
        (fun n => (Combinatorics.Sequence.balancedBlockCount (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) : ℝ)) atTop atTop ∧
      Tendsto
        (fun n => Combinatorics.Sequence.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n)) atTop atTop ∧
      Tendsto
        (fun n => Combinatorics.Sequence.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1) atTop atTop ∧
      Tendsto (fun n =>
        (Combinatorics.Sequence.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) : ℝ) /
          stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) ∧
      Tendsto (fun n =>
        ((Combinatorics.Sequence.balancedBlockShortLength (total n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1 : ℕ) : ℝ) /
          stableScaleTime α ν (scale n)) atTop (nhds (amplitude ^ α)) := by
  let reference : ℕ → ℕ := fun n => stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
      hα hα₂ hslow
  have hrefTop : Tendsto reference atTop atTop := by
    simpa [reference] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hrefDensity : Tendsto (fun n => (reference n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa [reference] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop hrate
  have hrefClock := tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
    hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hclockPos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (scale n) := by
    have hclockTop :=
      (stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow).comp
        hscaleTop
    exact hclockTop.eventually (eventually_gt_atTop 0)
  exact Asymptotics.tendsto_balancedBlockPartition_of_vanishingReference
    htotal hduration hrefTop hrefDensity hclockPos (by
      simpa [reference] using hrefClock)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

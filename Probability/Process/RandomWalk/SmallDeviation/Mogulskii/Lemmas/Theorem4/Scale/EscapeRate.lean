/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.SlowMultiplier
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic
import Analysis.Asymptotics.Scale.Block.Length
import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Inverse
/-!
# Stable centered-corridor probability on the rounded characteristic time scale

This module combines the stable centered-corridor escape rate with the rounded
regular-variation scale used in A. A. Mogul'skii, Theorem 4, Section 5,
equations (43)--(44):
\[
  \frac{B^*(x_n)}{\lfloor B^*(a_nx_n)\rfloor}
    \log \mathbb P_P(a_n^{-1}I_{-1}^{1}) \longrightarrow C.
\]

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.exists_tendsto_slowMultiplier_centeredCorridorLogRatio_of_escapeRate`
  chooses $a_n\to\infty$ with $a_nx_n/b_n\to0$ and proves the displayed
  logarithmic ratio for the path event $a_n^{-1}I_{-1}^{1}$, given its stable
  path-law escape rate $C$. The norming law and limiting stable path law are
  separate inputs. This combines the two preceding limits for the proof of
  Theorem 4, equation (44), and is kept in its proof-support module.

The cited result is A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081.
-/

open Filter MeasureTheory
open scoped Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

namespace IsStableMogulskiiScale

/-- Combine Lemma 1(II)'s centered-corridor escape rate with the rounded
scale relation in Mogul'skii's Theorem 4, Section 5, equation (44). -/
lemma exists_tendsto_slowMultiplier_centeredCorridorLogRatio_of_escapeRate
    {α : ℝ} {ν μ : Measure ℝ} [IsFiniteMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hα₀ : 0 < α) (hα_le_two : α ≤ 2)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {C : ℝ}
    (hEscape : HasStableCenteredCorridorEscapeRate α μ P C) :
    ∃ a : ℕ → ℝ, Monotone a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a n * (scale n / normalization n)) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (stableScaleTime α ν (scale n) /
          (Asymptotics.floorBlockLength
            (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ)) *
          Real.log ((P (stableProcessCenteredCorridor ((a n)⁻¹))).toReal))
        atTop (nhds C) := by
  obtain ⟨a, haMono, haTop, hsmall, hfloorRatio⟩ :=
    hscale.exists_tendsto_slowStableScaleTime_floor_scaleTime_ratio
      hslow hα₀ hα_le_two
  have hEscapeRate :=
    hEscape.tendsto_inv_rpow_mul_log
      (r := 1) (by norm_num : (0 : ℝ) < 1)
  have hlog := hEscapeRate.comp haTop
  have hax : Tendsto (fun n => a n * scale n) atTop atTop :=
    haTop.atTop_mul_atTop₀ hscale.scale_tendsto_atTop
  have hκtop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
    hα₀ hα_le_two hslow
  have hargument : Tendsto
      (fun n => stableScaleTime α ν (a n * scale n)) atTop atTop :=
    hκtop.comp hax
  have hfloorTop := Asymptotics.tendsto_floorBlockLength_atTop hargument
  have hfloorPos : ∀ᶠ n : ℕ in atTop,
      0 < (Asymptotics.floorBlockLength
        (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ) := by
    filter_upwards [hfloorTop.eventually_gt_atTop 0] with n hn
    exact_mod_cast hn
  have hκscale : Tendsto (fun n => stableScaleTime α ν (scale n))
      atTop atTop := hκtop.comp hscale.scale_tendsto_atTop
  have hκscalePos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (scale n) := hκscale.eventually_gt_atTop 0
  have haPos : ∀ᶠ n : ℕ in atTop, 0 < a n :=
    haTop.eventually_gt_atTop 0
  have haPowPos : ∀ᶠ n : ℕ in atTop, 0 < a n ^ α := by
    filter_upwards [haPos] with n han
    exact Real.rpow_pos_of_pos han α
  have hlog' : Tendsto (fun n =>
      (a n)⁻¹ ^ α *
        Real.log ((P (stableProcessCenteredCorridor ((a n)⁻¹))).toReal))
      atTop (nhds C) := by
    simpa [Function.comp_def, one_div] using hlog
  have hratioInv : Tendsto (fun n =>
      ((Asymptotics.floorBlockLength
        (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ) /
          (a n ^ α * stableScaleTime α ν (scale n)))⁻¹)
      atTop (nhds 1) := by
    simpa using hfloorRatio.inv₀ (by norm_num)
  have hproduct := hratioInv.mul hlog'
  have heq : (fun n =>
      (stableScaleTime α ν (scale n) /
        (Asymptotics.floorBlockLength
          (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ)) *
      Real.log ((P (stableProcessCenteredCorridor ((a n)⁻¹))).toReal)) =ᶠ[atTop]
      fun n =>
        ((Asymptotics.floorBlockLength
          (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ) /
          (a n ^ α * stableScaleTime α ν (scale n)))⁻¹ *
          ((a n)⁻¹ ^ α *
            Real.log ((P (stableProcessCenteredCorridor ((a n)⁻¹))).toReal)) := by
    filter_upwards [hfloorPos, hκscalePos, haPos, haPowPos] with
      n hfloor hnκ hna hnaPow
    have hfloor' : 0 < (Asymptotics.floorBlockLength
        (fun n => stableScaleTime α ν (a n * scale n)) n : ℝ) := hfloor
    have hpowInv : (a n)⁻¹ ^ α = (a n ^ α)⁻¹ :=
      Real.inv_rpow hna.le α
    rw [hpowInv]
    field_simp [hfloor'.ne', hnκ.ne', hnaPow.ne']
  refine ⟨a, haMono, haTop, hsmall, ?_⟩
  simpa only [one_mul] using hproduct.congr' heq.symm

end IsStableMogulskiiScale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

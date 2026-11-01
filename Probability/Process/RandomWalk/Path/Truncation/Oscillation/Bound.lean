/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Truncation.Asymptotic
public import Probability.Process.RandomWalk.Path.Truncation.Maximal.Basic
public import Analysis.Asymptotics.Scale.Block.Proportional
import all Probability.Process.RandomWalk.Path.Truncation.Oscillation.Lemmas.Scaling

/-!
# Eventual truncated maximal oscillation bound

For centered IID increments with finite second moment, this module gives the
eventual probability bound for the maximum over a fixed number of proportional
blocks. The limiting constant is the explicit fourth-moment expression
computed by the internal scaling lemmas.

## Public declarations

* `eventually_measure_exists_block_exists_abs_ge_lt` states that if
  `blocks * ENNReal.ofReal ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
  3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2) / threshold ^ 4) < bound`, then
  eventually the IID probability of a block partial sum of size at least
  `threshold * sqrt n` among the first `blocks` proportional blocks is less
  than `bound`.

Writing \(L_n=\mathrm{proportionalBlockLength}(\mathrm{fraction},n)\),
under this moment budget, for all sufficiently large \(n\),
\(\mathbb P_\nu\{\exists j<\mathrm{blocks},\exists k\le L_n,
|S_{jL_n+k+1}-S_{jL_n}|\ge\mathrm{threshold}\sqrt n\}
<\mathrm{bound}\).
-/

open Filter MeasureTheory ProbabilityTheory Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Asymptotics

/-- Eventual form of the global proportional-block oscillation estimate.
Any strict upper bound on the explicit limiting right-hand side eventually
controls the actual IID path probability. -/
theorem eventually_measure_exists_block_exists_abs_ge_lt
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : Integrable (fun x : ℝ => x ^ 2) ν)
    (hcentered : (∫ x : ℝ, x ∂ν) = 0)
    (blocks : ℕ) {fraction cutoff threshold : ℝ}
    (hfraction : 0 < fraction) (hcutoff : 0 < cutoff)
    (hthreshold : 0 < threshold) {bound : ENNReal}
    (hbound : (blocks : ENNReal) * ENNReal.ofReal
        ((8 * (fraction * cutoff ^ 2 * ∫ x, x ^ 2 ∂ν) +
          3 * fraction ^ 2 * (∫ x, x ^ 2 ∂ν) ^ 2) /
            threshold ^ 4) < bound) :
    ∀ᶠ n : ℕ in atTop,
      (iidSequenceLaw ν) {path |
        ∃ j < blocks,
          ∃ k ∈ Finset.range (proportionalBlockLength fraction n + 1),
            threshold * Real.sqrt n ≤
              |AdditivePath.blockSum (j * proportionalBlockLength fraction n) (k + 1) path|} <
        bound := by
  let gap : ℕ → ℝ := fun n => threshold * Real.sqrt n -
    ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
      |truncatedIncrementMean ν (cutoff * Real.sqrt n)|
  have hbias :=
    tendsto_proportionalBlock_mul_abs_truncatedMean_div_sqrt_zero
      ν hsq hcentered hfraction hcutoff
  have hgapRatio : Tendsto (fun n => gap n / Real.sqrt n)
      atTop (nhds threshold) := by
    have hconst : Tendsto (fun _ : ℕ => threshold) atTop (nhds threshold) :=
      tendsto_const_nhds
    have h := hconst.sub hbias
    have h' : Tendsto (fun n : ℕ => threshold -
        (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)|) /
            Real.sqrt n) atTop (nhds threshold) := by
      simpa using h
    apply h'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    dsimp only [gap]
    field_simp [hsqrtPos.ne']
  have hgapPos : ∀ᶠ n in atTop, 0 < gap n := by
    have hratioPos : ∀ᶠ n in atTop, threshold / 2 < gap n / Real.sqrt n :=
      hgapRatio.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hratioPos, eventually_gt_atTop 0] with n hnRatio hn
    have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hratio : 0 < gap n / Real.sqrt n := lt_of_lt_of_le
      (half_pos hthreshold) hnRatio.le
    have hmul := mul_pos hratio hsqrtPos
    simpa [div_mul_cancel₀ _ hsqrtPos.ne'] using hmul
  have hlimit := tendsto_proportionalBlock_oscillationBound
    ν hsq hcentered blocks hfraction hcutoff hthreshold
  have hright : ∀ᶠ n : ℕ in atTop,
      ((blocks * proportionalBlockLength fraction n + 1 : ℕ) : ENNReal) *
          ν {x | cutoff * Real.sqrt n < |x|} +
        (blocks : ENNReal) *
          centeredTruncatedFourthBound ν (cutoff * Real.sqrt n)
            (proportionalBlockLength fraction n) (gap n) < bound :=
    hlimit.eventually (Iio_mem_nhds hbound)
  filter_upwards [hgapPos, hright] with n hgapN hrightN
  have hgapN' :
      ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) *
          |truncatedIncrementMean ν (cutoff * Real.sqrt n)| <
        threshold * Real.sqrt n := by
    exact sub_pos.mp (show 0 < gap n from hgapN)
  exact (measure_exists_block_exists_abs_ge_le_of_truncation
    ν hsq (mul_nonneg hcutoff.le (Real.sqrt_nonneg _)) blocks
    (proportionalBlockLength fraction n) hgapN').trans_lt hrightN

end ProbabilityTheory.RandomWalk

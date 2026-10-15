/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.RangeRate

/-!
# Reindexing the source-path range rate to block lengths

The public theorem is
`eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_rangeRate_reindex`:
if a block of length $\ell_n$ has spatial width $\Delta_n$ matching the
source scale and $d<\pi^2\mathcal E_k/2$, then its oscillation probability
is eventually bounded by
$\exp\bigl(-d(\ell_n+1)/(a^2\Delta_n^2)\bigr)$,
where $a$ is the scale-to-width factor in the theorem statement.

The source-path Mogul'skii rate bounds a block oscillation event when the
spatial scale is a small-deviation scale along the block horizon. This file
packages that bound for an independently indexed sequence of horizons and
spatial widths. It supplies a raw-increment-law one-block estimate, without a
Brownian-process witness.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Reindex the sharp source-path range-rate estimate along arbitrary block
lengths. The displayed `scale` condition is the substantive long-block
condition: along the chosen lengths, the width grows while its ratio to the
square root of the block horizon tends to zero. -/
theorem eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_rangeRate_reindex
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {scale : ℕ → ℝ}
    (hscale : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    {length : ℕ → ℕ} {delta : ℕ → ℝ}
    (hindex : Tendsto (fun n => length n + 1) atTop atTop)
    {factor eta rate : ℝ} (hfactor : 1 < factor) (heta : 0 < eta)
    (hrate : 0 < rate) (k : ℕ) (hk : 0 < k)
    (hrate_lt : rate < (Real.pi ^ 2 / 2) *
      (rangeCoverUnion k hk).realEnergy)
    (hscaleBlock : ∀ᶠ n : ℕ in atTop,
      scale (length n + 1) = (factor * (1 + eta) / 2) * delta n) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length n) increment ∈
          blockOscillationEvent ((1 + eta) * delta n) (length n)} ≤
        ENNReal.ofReal (Real.exp
          (-(rate / (factor * (1 + eta) / 2) ^ 2) *
            (((length n + 1 : ℕ) : ℝ) / delta n ^ 2))) := by
  have hbase :=
    eventually_iidSequenceLaw_blockOscillationProbability_le_exp_of_centeredUnitVariance_rangeCover
      ν hcentered hsquare hvariance hscale hfactor hrate k hk hrate_lt
  have hbase' : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0
          ((length n + 1) - 1) increment ∈
            blockOscillationEvent
              (2 * scale (length n + 1) / factor)
              ((length n + 1) - 1)} ≤
        ENNReal.ofReal (Real.exp
          (-rate * (((length n + 1 : ℕ) : ℝ) /
            scale (length n + 1) ^ 2))) := by
    exact hindex.eventually hbase
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale (length n + 1) :=
    hindex.eventually (Asymptotics.IsSmallDeviationScale.eventually_pos hscale)
  filter_upwards [hbase', hscaleBlock, hscalePos] with n hprob hscaleEq hscalePosAt
  have hdeltaPos : 0 < delta n := by
    have hcoef : 0 < factor * (1 + eta) / 2 := by positivity
    have hprod : 0 < (factor * (1 + eta) / 2) * delta n := by
      simpa [hscaleEq] using hscalePosAt
    by_contra hnot
    have hδ : delta n ≤ 0 := le_of_not_gt hnot
    have hprod' : (factor * (1 + eta) / 2) * delta n ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef.le hδ
    linarith
  have hfactorPos : 0 < factor := by linarith
  have hwidth : 2 * scale (length n + 1) / factor =
      (1 + eta) * delta n := by
    rw [hscaleEq]
    field_simp [ne_of_gt hfactorPos]
  have hexponent : rate * (((length n + 1 : ℕ) : ℝ) /
      scale (length n + 1) ^ 2) =
      (rate / (factor * (1 + eta) / 2) ^ 2) *
        (((length n + 1 : ℕ) : ℝ) / delta n ^ 2) := by
    rw [hscaleEq]
    field_simp [ne_of_gt hdeltaPos, ne_of_gt hfactorPos]
  have hprob' :
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length n) increment ∈
          blockOscillationEvent ((1 + eta) * delta n) (length n)} ≤
        ENNReal.ofReal (Real.exp
          (-(rate / (factor * (1 + eta) / 2) ^ 2) *
            (((length n + 1 : ℕ) : ℝ) / delta n ^ 2))) := by
    have hlen : (length n + 1) - 1 = length n := Nat.add_sub_cancel_right _ _
    rw [hlen, hwidth] at hprob
    rw [neg_mul, hexponent] at hprob
    simpa [neg_mul, mul_assoc, mul_comm, mul_left_comm] using hprob
  exact hprob'

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

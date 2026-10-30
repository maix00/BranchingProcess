/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Scale.Block.Length
import Combinatorics.Sequence.BalancedPartition
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockLength
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.BlockCount
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Mathlib.Data.Nat.ModEq

/-!
# Balanced endpoint-core block count

This module proves the proof-specific count limit for the endpoint-core partition
that reserves one stable block for the final bridge. If the total horizon
satisfies $N_n/n\to\tau>0$, then
\[
  r_n\left(\operatorname{balancedBlockCount}(N_n-b_n,b_n)+1\right)
    \longrightarrow \frac{\tau}{a^\alpha},
\]
where $b_n$ is the stable block length at amplitude $a$ and $r_n$ is the
stable small-deviation rate. The segment-count limit in
`Stable/Scale/BlockCount.lean` supplies the asymptotics. This module identifies
the endpoint-core quotient with the full-horizon quotient once the reserved
block fits inside the horizon.

The endpoint-core block count occurs in the finite-partition argument for
Theorem 1, equation (15), of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount`:
  for $0<\alpha\leq2$, $a>0$, a stable Mogulskii scale with slowly varying
  factor, and $N_n/n\to\tau>0$, if the stable block length $b_n$ satisfies
  $b_n/n\to0$ and the stable rate $r_n\to0$, then
  \[
    r_n\left(\operatorname{balancedBlockCount}(N_n-b_n,b_n)+1\right)
      \longrightarrow \frac{\tau}{a^\alpha},
  \]
  where
  $b_n=\operatorname{stableBlockLength}(\alpha,\nu,a^\alpha,\mathrm{scale},n)$
  and
  $r_n=\operatorname{stableSmallDeviationRate}(\alpha,\nu,\mathrm{scale},n)$.
-/

section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Reserving one block and adding it back preserves the quotient count. -/
private lemma balancedCoreBridgeCount_eq_quotient
    {total blockLength : ℕ} (hblock : 0 < blockLength)
    (hle : blockLength ≤ total) :
    Combinatorics.Sequence.balancedBlockCount (total - blockLength) blockLength + 1 =
      total / blockLength := by
  change (total - blockLength) / blockLength + 1 = total / blockLength
  have htotal : total - blockLength + blockLength = total :=
    Nat.sub_add_cancel hle
  conv_rhs => rw [← htotal]
  rw [Nat.add_div_of_dvd_left (dvd_refl blockLength)]
  rw [Nat.div_self hblock]

/-- The balanced endpoint-core partition reserves one stable block for the
terminal bridge. Its main-block quotient plus that bridge equals the quotient
for the full horizon once the block length is at most the horizon, so the
stable-scale segment-count limit applies directly. -/
lemma tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount
    {α duration amplitude : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hamplitude : 0 < amplitude)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hduration : 0 < duration)
    (total : ℕ → ℕ)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    Tendsto
      (fun n => stableSmallDeviationRate α ν scale n *
        (((Combinatorics.Sequence.balancedBlockCount
          (total n - stableBlockLength α ν (amplitude ^ α) scale n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1 : ℕ) : ℝ)))
      atTop (nhds (duration / amplitude ^ α)) := by
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop := hscale.scale_tendsto_atTop
  have hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
      hα hα₂ hslow
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n := by
    simpa [blockLength] using eventually_stableBlockLength_pos_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hblockRatio : Tendsto (fun n => (blockLength n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa [blockLength] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop hrate
  have hblockLe : ∀ᶠ n : ℕ in atTop, blockLength n ≤ total n :=
    Asymptotics.eventually_block_le_horizon_of_positive_density
      htotal hblockRatio hduration
  have hsegment : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n *
        ((total n / blockLength n : ℕ) : ℝ))
      atTop (nhds (duration / amplitude ^ α)) := by
    simpa [blockLength] using
      tendsto_stableScaleTime_div_nat_mul_segmentBlockCount
        hα hα₂ (Real.rpow_pos_of_pos hamplitude α) hscale hslow htotal
  have hcountEq : (fun n => stableSmallDeviationRate α ν scale n *
      ((total n / blockLength n : ℕ) : ℝ)) =ᶠ[atTop]
      fun n => stableSmallDeviationRate α ν scale n *
        (((Combinatorics.Sequence.balancedBlockCount
          (total n - blockLength n) (blockLength n) + 1 : ℕ) : ℝ)) := by
    filter_upwards [hblockPos, hblockLe] with n hblock hle
    rw [balancedCoreBridgeCount_eq_quotient hblock hle]
  exact hsegment.congr' hcountEq

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end

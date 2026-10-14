/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.NarrowedWidth

/-!
# Rounded width under the staircase block scale

The public theorem in this file is:

- `eventually_staircaseRateComparison_of_blockScale`:
  if $\ell_n/\Delta_n^3\to0$ and $d<d''\beta^2$, then
  $d\Delta_n^2\le
  d''\lfloor\beta(\Delta_n-2c\ell_n/\Delta_n^2)\rfloor^2$
  eventually.

This is the rounded-width comparison in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The block-scale condition supplies the negligible width loss
and hence the sharp rounded exponent comparison. -/
theorem eventually_staircaseRateComparison_of_blockScale
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {drift beta narrowedRate blockRate : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hscale : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0))
    (hrate : narrowedRate < blockRate * beta ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      narrowedRate * width n ^ 2 ≤
        blockRate *
          (⌊beta * (width n - 2 * drift * (blockLength n : ℝ) /
            width n ^ 2)⌋₊ : ℝ) ^ 2 := by
  let loss : ℕ → ℝ := fun n =>
    2 * drift * (blockLength n : ℝ) / width n ^ 2
  have hloss : Tendsto (fun n => loss n / width n)
      atTop (𝓝 0) := by
    have hscaled : Tendsto (fun n =>
        (2 * drift) * ((blockLength n : ℝ) / width n ^ 3))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hscale
    have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
      hwidth.eventually (eventually_gt_atTop 0)
    apply hscaled.congr'
    filter_upwards [hwidthPos] with n hn
    dsimp [loss]
    field_simp [ne_of_gt hn]
  have hrelative := Asymptotics.tendsto_widthMinusLoss_div_width hwidth hloss
  simpa only [loss] using
    Asymptotics.eventually_rateComparison_of_floor_width hbeta hwidth hrelative hrate

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

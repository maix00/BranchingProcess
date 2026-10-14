/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseEndpointLimit
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BinParameters
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseRateLimit

/-!
# A common threshold for every staircase block

The public theorem in this file is:

- `eventually_staircaseGlobalConditions`:
  under $\Delta_n\to\infty$,
  $\Delta_n^2/\ell_n\to0$, and
  $\ell_n/\Delta_n^3\to0$, the strict fixed rate and endpoint margins
  imply all global numeric inequalities for the concrete staircase at
  sufficiently large $n$.

This is the common-threshold assertion in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The two endpoint intervals correspond to
the ordinary and final block cases in that proof.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- All width, time, rate, and endpoint inequalities used by the finite
staircase hold under the paper's superquadratic and subcubic block scale. -/
theorem eventually_staircaseGlobalConditions
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {drift margin endpointFraction narrowedRate blockRate
      uInterior vInterior uFinal vFinal : ℝ}
    (m : ℕ) (hm : 2 ≤ m)
    (hwidth : Tendsto width atTop atTop)
    (hlength : ∀ᶠ n : ℕ in atTop, 0 < blockLength n)
    (hquadratic : Tendsto (fun n =>
      width n ^ 2 / (blockLength n : ℝ)) atTop (𝓝 0))
    (hcubic : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0))
    (hrate : narrowedRate < blockRate * staircaseBinWidth m ^ 2)
    (hinteriorLower : (1 / 3 : ℝ) / staircaseBinWidth m +
      margin < uInterior)
    (hinteriorUpper : vInterior + margin ≤
      ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (hfinalLower : margin ≤ uFinal)
    (hfinalUpper : vFinal + margin ≤
      (endpointFraction - 1 / (3 * (m : ℝ))) /
        staircaseBinWidth m)
    (width₀ ratio₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      0 < width n ∧
      0 < blockLength n ∧
      10 * drift * (blockLength n : ℝ) < width n ^ 3 ∧
      width₀ ≤ ⌊staircaseBinWidth m * (width n / 2)⌋₊ ∧
      1 / margin ≤ staircaseBinWidth m * (width n / 2) ∧
      ratio₀ * ⌊staircaseBinWidth m * width n⌋₊ ^ 2 ≤
        blockLength n ∧
      narrowedRate * width n ^ 2 ≤
        blockRate *
          (⌊staircaseBinWidth m *
            (width n - 2 * drift * (blockLength n : ℝ) /
              width n ^ 2)⌋₊ : ℝ) ^ 2 ∧
      ((width n / 3 + (2 / 3 : ℝ) *
          (2 * drift * (blockLength n : ℝ) / width n ^ 2)) /
          (width n -
            2 * drift * (blockLength n : ℝ) / width n ^ 2)) /
        staircaseBinWidth m + margin ≤ uInterior ∧
      vInterior + margin ≤
        ((2 / 3 : ℝ) - 1 / (3 * (m : ℝ))) /
          staircaseBinWidth m ∧
      margin ≤ uFinal ∧
      vFinal + margin ≤
        (endpointFraction - 1 / (3 * (m : ℝ))) /
          staircaseBinWidth m := by
  have hbeta : 0 < staircaseBinWidth m := staircaseBinWidth_pos hm
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hcost := Asymptotics.eventually_linear_block_cost_lt_width_cubed hwidth hcubic
    (coefficient := 10 * drift)
  have hfloor := Asymptotics.eventually_floor_half_width_ge hbeta
    hwidth width₀
  have hmarginWidth := Asymptotics.eventually_half_width_ge_inverse_margin hbeta hwidth
    (margin := margin)
  have htime := Asymptotics.eventually_floor_width_sq_le_blockLength hbeta hwidth
    hlength hquadratic ratio₀
  have hrate' := eventually_staircaseRateComparison_of_blockScale
    hbeta hwidth hcubic hrate (drift := drift)
  have hinteriorLower' :=
    eventually_staircaseInteriorLowerMargin_of_blockScale
      hbeta hwidth hcubic hinteriorLower (drift := drift)
  filter_upwards [hwidthPos, hlength, hcost, hfloor, hmarginWidth,
    htime, hrate', hinteriorLower']
    with n hnWidth hnLength hnCost hnFloor hnMargin hnTime hnRate hnLower
  exact ⟨hnWidth, hnLength, hnCost, hnFloor, hnMargin, hnTime,
    hnRate, hnLower, hinteriorUpper, hfinalLower, hfinalUpper⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

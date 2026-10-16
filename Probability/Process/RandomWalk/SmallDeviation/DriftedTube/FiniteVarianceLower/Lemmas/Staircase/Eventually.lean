/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Endpoint.Limit
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Binning.Parameters
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Rate.Limit
/-!
# A common threshold for every staircase block

The module-visible supporting lemma in this file is:

- `eventually_staircaseGlobalConditions`:
  under $\Delta_n\to\infty$,
  $\Delta_n^2/\ell_n\to0$, and
  $\ell_n/\Delta_n^3\to0$, the strict fixed rate and endpoint margins
  imply all global numeric inequalities for the concrete staircase at
  sufficiently large $n$.
- `eventually_staircaseUpperEndpointGlobalConditions`:
  the same width, time, and rate conditions with the final endpoint
  interval adjacent to the upper edge.

This is the common-threshold assertion in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5. The two endpoint intervals correspond to
the ordinary and final block cases in that proof.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lower rounded half-width passes every fixed integer threshold. -/
private lemma eventually_floor_half_width_ge
    {width : ℕ → ℝ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (width₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      width₀ ≤ ⌊beta * (width n / 2)⌋₊ := by
  have hscaled : Tendsto (fun n => beta * (width n / 2))
      atTop atTop := by
    convert hwidth.const_mul_atTop (div_pos hbeta (by norm_num : (0 : ℝ) < 2))
      using 1
    ext n
    ring
  exact (tendsto_nat_floor_atTop.comp hscaled).eventually
    (eventually_ge_atTop width₀)

/-- A fixed positive endpoint margin fits inside the narrowed half-width
when the global width tends to infinity. -/
private lemma eventually_half_width_ge_inverse_margin
    {width : ℕ → ℝ} {beta margin : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      1 / margin ≤ beta * (width n / 2) := by
  have hscaled : Tendsto (fun n => beta * (width n / 2))
      atTop atTop := by
    convert hwidth.const_mul_atTop (div_pos hbeta (by norm_num : (0 : ℝ) < 2))
      using 1
    ext n
    ring
  exact hscaled.eventually (eventually_ge_atTop (1 / margin))

/-- The superquadratic block length eventually dominates every fixed
integer multiple of the squared rounded narrowed width. -/
private lemma eventually_floor_width_sq_le_blockLength
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {beta : ℝ} (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hlength : ∀ᶠ n : ℕ in atTop, 0 < blockLength n)
    (hscale : Tendsto (fun n => width n ^ 2 / (blockLength n : ℝ))
      atTop (𝓝 0))
    (ratio₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ratio₀ * ⌊beta * width n⌋₊ ^ 2 ≤ blockLength n := by
  have hscaled : Tendsto (fun n =>
      ((ratio₀ : ℝ) * beta ^ 2) *
        (width n ^ 2 / (blockLength n : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hscale
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((ratio₀ : ℝ) * beta ^ 2) *
        (width n ^ 2 / (blockLength n : ℝ)) < 1 :=
    hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  filter_upwards [hlength, hsmall, hwidthPos]
    with n hlengthN hsmallN hwidthN
  have hlengthReal : 0 < (blockLength n : ℝ) := by exact_mod_cast hlengthN
  have hfloor : (⌊beta * width n⌋₊ : ℝ) ≤ beta * width n :=
    Nat.floor_le (mul_nonneg hbeta.le hwidthN.le)
  have hsquare : (⌊beta * width n⌋₊ : ℝ) ^ 2 ≤
      (beta * width n) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 2
  have hreal : (ratio₀ : ℝ) * (⌊beta * width n⌋₊ : ℝ) ^ 2 ≤
      (blockLength n : ℝ) := by
    have hdiv :
        (ratio₀ : ℝ) * (beta * width n) ^ 2 /
            (blockLength n : ℝ) < 1 := by
      convert hsmallN using 1
      ring
    have hupper := (div_lt_iff₀ hlengthReal).1 hdiv
    nlinarith [mul_le_mul_of_nonneg_left hsquare
      (Nat.cast_nonneg ratio₀)]
  exact_mod_cast hreal

/-- A subcubic block length is eventually smaller than the cube of the
width after multiplication by any fixed real coefficient. -/
private lemma eventually_linear_block_cost_lt_width_cubed
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ} {coefficient : ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hscale : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      coefficient * (blockLength n : ℝ) < width n ^ 3 := by
  have hscaled : Tendsto (fun n =>
      coefficient * ((blockLength n : ℝ) / width n ^ 3))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hscale
  have hsmall : ∀ᶠ n : ℕ in atTop,
      coefficient * ((blockLength n : ℝ) / width n ^ 3) < 1 :=
    hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall, hwidthPos] with n hsmallN hwidthN
  have heq : coefficient * ((blockLength n : ℝ) / width n ^ 3) =
      coefficient * (blockLength n : ℝ) / width n ^ 3 := by ring
  rw [heq] at hsmallN
  simpa only [one_mul] using
    (div_lt_iff₀ (pow_pos hwidthN _)).1 hsmallN

/-- All width, time, rate, and endpoint inequalities used by the finite
staircase hold under the superquadratic and subcubic block scale of Wang Yiyang's Lemma 3.5. -/
lemma eventually_staircaseGlobalConditions
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
  have hcost := eventually_linear_block_cost_lt_width_cubed hwidth hcubic
    (coefficient := 10 * drift)
  have hfloor := eventually_floor_half_width_ge hbeta
    hwidth width₀
  have hmarginWidth := eventually_half_width_ge_inverse_margin hbeta hwidth
    (margin := margin)
  have htime := eventually_floor_width_sq_le_blockLength hbeta hwidth
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

/-- The common staircase threshold also supports a final window next to
the upper boundary of the rising tube. -/
lemma eventually_staircaseUpperEndpointGlobalConditions
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
    (hfinalLower : max (1 - endpointFraction) 0 /
        staircaseBinWidth m + margin < uFinal)
    (hfinalUpper : vFinal + margin ≤
      (1 - 1 / (3 * (m : ℝ))) /
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
      (max (1 - endpointFraction) 0 * width n /
          (width n -
            2 * drift * (blockLength n : ℝ) / width n ^ 2)) /
        staircaseBinWidth m + margin ≤ uFinal ∧
      vFinal + margin ≤
        (1 - 1 / (3 * (m : ℝ))) /
          staircaseBinWidth m := by
  have hbase := eventually_staircaseGlobalConditions
    (drift := drift) (endpointFraction := 1) (uFinal := margin)
    (vFinal := (1 - 1 / (3 * (m : ℝ))) /
      staircaseBinWidth m - margin)
    m hm hwidth hlength hquadratic hcubic hrate
    hinteriorLower hinteriorUpper (le_refl margin)
    (by simp) width₀ ratio₀
  have hlast := eventually_staircaseUpperFinalLowerMargin_of_blockScale
    (drift := drift) (endpointFraction := endpointFraction)
    (staircaseBinWidth_pos hm) hwidth hcubic hfinalLower
  filter_upwards [hbase, hlast] with n hn hnLast
  obtain ⟨hnWidth, hnLength, hnCost, hnFloor, hnMargin,
    hnTime, hnRate, hnLower, hnUpper, _, _⟩ := hn
  exact ⟨hnWidth, hnLength, hnCost, hnFloor, hnMargin,
    hnTime, hnRate, hnLower, hnUpper, hnLast, hfinalUpper⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

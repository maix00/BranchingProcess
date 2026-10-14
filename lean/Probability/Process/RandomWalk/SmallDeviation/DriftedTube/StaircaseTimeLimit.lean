/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseRateLimit

/-!
# Time-to-width condition for the staircase blocks

The public theorems in this file are:

- `eventually_staircaseHalfWidthThreshold`:
  for fixed $W_0$ and $\beta>0$,
  $W_0\le\lfloor\beta\Delta_n/2\rfloor$ eventually.
- `eventually_staircaseMarginWidth`:
  for fixed $\varepsilon>0$,
  $1/\varepsilon\le\beta\Delta_n/2$ eventually.
- `eventually_staircaseTimeRatio`:
  if $\Delta_n^2/\ell_n\to0$ and $\ell_n>0$ eventually, then for every
  fixed $R\in\mathbb N$ and $\beta>0$,
  $R\lfloor\beta\Delta_n\rfloor^2\le\ell_n$ eventually.
- `eventually_staircaseCost`:
  $\ell_n/\Delta_n^3\to0$ implies
  $10c\ell_n<\Delta_n^3$ eventually for fixed drift $c$.

This is the block-time condition $\ell/\Delta^2\to\infty$ in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lower rounded half-width passes every fixed integer threshold. -/
theorem eventually_staircaseHalfWidthThreshold
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
theorem eventually_staircaseMarginWidth
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
theorem eventually_staircaseTimeRatio
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

/-- The subcubic block scale supplies the robust entrance and staircase
geometry inequality for all sufficiently large widths. -/
theorem eventually_staircaseCost
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ} {drift : ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hscale : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      10 * drift * (blockLength n : ℝ) < width n ^ 3 := by
  have hscaled : Tendsto (fun n =>
      (10 * drift) * ((blockLength n : ℝ) / width n ^ 3))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hscale
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (10 * drift) * ((blockLength n : ℝ) / width n ^ 3) < 1 :=
    hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  filter_upwards [hsmall, hwidthPos] with n hsmallN hwidthN
  have heq : (10 * drift) * ((blockLength n : ℝ) / width n ^ 3) =
      10 * drift * (blockLength n : ℝ) / width n ^ 3 := by ring
  rw [heq] at hsmallN
  simpa only [one_mul] using
    (div_lt_iff₀ (pow_pos hwidthN _)).1 hsmallN

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

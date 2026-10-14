/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.BlockScale

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

/-- A negligible block-width loss gives the actual-to-global width ratio
used in the staircase proof. -/
private theorem tendsto_widthMinusLoss_div_width
    {width loss : ℕ → ℝ}
    (hwidth : Tendsto width atTop atTop)
    (hloss : Tendsto (fun n => loss n / width n) atTop (𝓝 0)) :
    Tendsto (fun n => (width n - loss n) / width n)
      atTop (𝓝 1) := by
  have hbase : Tendsto (fun n => 1 - loss n / width n)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hloss
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  apply hbase.congr'
  filter_upwards [hwidthPos] with n hn
  field_simp [ne_of_gt hn]

/-- The floor of the narrowed horizontal width has the same asymptotic
global-width ratio as the unrounded width. -/
private theorem tendsto_floor_narrowedWidth_div_globalWidth
    {width loss : ℕ → ℝ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hrelative : Tendsto (fun n => (width n - loss n) / width n)
      atTop (𝓝 1)) :
    Tendsto (fun n =>
      (⌊beta * (width n - loss n)⌋₊ : ℝ) / width n)
      atTop (𝓝 beta) := by
  have hnarrowed : Tendsto (fun n => beta * (width n - loss n))
      atTop atTop := by
    have hhalf : ∀ᶠ n : ℕ in atTop,
        1 / 2 ≤ (width n - loss n) / width n :=
      hrelative.eventually (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
      hwidth.eventually (eventually_gt_atTop 0)
    apply Filter.tendsto_atTop.2
    intro b
    have hlarge := hwidth.eventually
      (eventually_ge_atTop (max 0 (2 * b / beta)))
    filter_upwards [hhalf, hwidthPos, hlarge] with n hhalfN hwidthN hlargeN
    have hidentity : beta * (width n - loss n) =
        beta * width n * ((width n - loss n) / width n) := by
      field_simp
    rw [hidentity]
    have hscaled : 2 * b ≤ beta * width n := by
      have hb := le_trans (le_max_right _ _) hlargeN
      have hb' := (div_le_iff₀ hbeta).1 hb
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hhalfN
      (mul_pos hbeta hwidthN).le
    nlinarith [hmul]
  have hfloor : Tendsto (fun n =>
      (⌊beta * (width n - loss n)⌋₊ : ℝ) /
        (beta * (width n - loss n))) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hnarrowed
  have hscaled : Tendsto (fun n =>
      beta * ((width n - loss n) / width n)) atTop (𝓝 beta) := by
    simpa using tendsto_const_nhds.mul hrelative
  have hproduct := hfloor.mul hscaled
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hnarrowedPos : ∀ᶠ n : ℕ in atTop,
      0 < beta * (width n - loss n) :=
    hnarrowed.eventually (eventually_gt_atTop 0)
  have hproductEq :
      (fun n =>
        (⌊beta * (width n - loss n)⌋₊ : ℝ) /
          (beta * (width n - loss n)) *
            (beta * ((width n - loss n) / width n))) =ᶠ[atTop]
      (fun n =>
        (⌊beta * (width n - loss n)⌋₊ : ℝ) / width n) := by
    filter_upwards [hwidthPos, hnarrowedPos] with n hwidthN hnarrowedN
    have hdiff : width n - loss n ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hnarrowedN
      exact (not_lt_of_ge le_rfl) hnarrowedN
    field_simp [ne_of_gt hwidthN, hdiff, ne_of_gt hbeta]
  simpa only [one_mul] using hproduct.congr' hproductEq

/-- A strict rate margin survives rounding the narrowed width. -/
private theorem eventually_rateComparison_of_floor_width
    {width loss : ℕ → ℝ} {beta narrowedRate blockRate : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hrelative : Tendsto (fun n => (width n - loss n) / width n)
      atTop (𝓝 1))
    (hrate : narrowedRate < blockRate * beta ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      narrowedRate * width n ^ 2 ≤
        blockRate * (⌊beta * (width n - loss n)⌋₊ : ℝ) ^ 2 := by
  have hratio := tendsto_floor_narrowedWidth_div_globalWidth
    hbeta hwidth hrelative
  have hscaled : Tendsto (fun n =>
      blockRate *
        ((⌊beta * (width n - loss n)⌋₊ : ℝ) / width n) ^ 2)
      atTop (𝓝 (blockRate * beta ^ 2)) :=
    tendsto_const_nhds.mul (hratio.pow 2)
  have hmargin := hscaled.eventually (eventually_gt_nhds hrate)
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  filter_upwards [hmargin, hwidthPos] with n hn hwidthN
  have hsq : 0 < width n ^ 2 := sq_pos_of_pos hwidthN
  have hratioEq :
      blockRate *
          ((⌊beta * (width n - loss n)⌋₊ : ℝ) / width n) ^ 2 =
        blockRate * (⌊beta * (width n - loss n)⌋₊ : ℝ) ^ 2 /
          width n ^ 2 := by ring
  rw [hratioEq] at hn
  exact (le_div_iff₀ hsq).1 hn.le

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
  have hrelative := tendsto_widthMinusLoss_div_width hwidth hloss
  simpa only [loss] using
    eventually_rateComparison_of_floor_width hbeta hwidth hrelative hrate

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

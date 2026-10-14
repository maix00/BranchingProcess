/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseTimeLimit

/-!
# Interior endpoint ratio for the staircase blocks

The public theorems in this file are:

- `tendsto_staircaseInteriorLowerRatio`:
  if $D_n/\Delta_n\to0$, then
  $\bigl((\Delta_n/3+2D_n/3)/(\Delta_n-D_n)\bigr)/\beta
  \to 1/(3\beta)$.
- `eventually_staircaseInteriorLowerMargin`:
  if $1/(3\beta)+\varepsilon<u$, the ordinary-block endpoint lower
  margin condition holds eventually.
- `eventually_staircaseInteriorLowerMargin_of_blockScale`:
  the same conclusion follows directly from
  $\ell_n/\Delta_n^3\to0$ for fixed drift $c$.

These are the ordinary-block endpoint comparisons in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open Filter
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lower endpoint fraction of the next central window approaches
$1/(3\beta)$ after narrowing the horizontal tube. -/
theorem tendsto_staircaseInteriorLowerRatio
    {width loss : ℕ → ℝ} {beta : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hloss : Tendsto (fun n => loss n / width n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ((width n / 3 + (2 / 3 : ℝ) * loss n) /
        (width n - loss n)) / beta)
      atTop (𝓝 ((1 / 3 : ℝ) / beta)) := by
  let x : ℕ → ℝ := fun n => loss n / width n
  have hx : Tendsto x atTop (𝓝 0) := hloss
  have hnum : Tendsto (fun n => (1 / 3 : ℝ) + (2 / 3) * x n)
      atTop (𝓝 (1 / 3 : ℝ)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hx) using 1
    simp
  have hden : Tendsto (fun n => 1 - x n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hx
  have hratio : Tendsto (fun n =>
      ((1 / 3 : ℝ) + (2 / 3) * x n) / (1 - x n) / beta)
      atTop (𝓝 ((1 / 3 : ℝ) / beta)) := by
    convert (hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).div
      tendsto_const_nhds (ne_of_gt hbeta) using 1
    simp
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  apply hratio.congr'
  filter_upwards [hwidthPos] with n hn
  dsimp [x]
  have hne : width n ≠ 0 := ne_of_gt hn
  field_simp [hne]

/-- A strict lower endpoint margin remains valid for all sufficiently
large ordinary staircase blocks. -/
theorem eventually_staircaseInteriorLowerMargin
    {width loss : ℕ → ℝ} {beta margin uInterior : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hloss : Tendsto (fun n => loss n / width n) atTop (𝓝 0))
    (hmargin : (1 / 3 : ℝ) / beta + margin < uInterior) :
    ∀ᶠ n : ℕ in atTop,
      ((width n / 3 + (2 / 3 : ℝ) * loss n) /
          (width n - loss n)) / beta + margin ≤ uInterior := by
  have hratio := tendsto_staircaseInteriorLowerRatio hbeta hwidth hloss
  have hsum : Tendsto (fun n =>
      ((width n / 3 + (2 / 3 : ℝ) * loss n) /
          (width n - loss n)) / beta + margin)
      atTop (𝓝 ((1 / 3 : ℝ) / beta + margin)) := by
    simpa using hratio.add tendsto_const_nhds
  exact (hsum.eventually (eventually_lt_nhds hmargin)).mono
    (fun n hn => hn.le)

/-- The paper's subcubic block-scale condition gives the ordinary-block
lower endpoint margin with one common width threshold. -/
theorem eventually_staircaseInteriorLowerMargin_of_blockScale
    {width : ℕ → ℝ} {blockLength : ℕ → ℕ}
    {drift beta margin uInterior : ℝ}
    (hbeta : 0 < beta)
    (hwidth : Tendsto width atTop atTop)
    (hscale : Tendsto (fun n =>
      (blockLength n : ℝ) / width n ^ 3) atTop (𝓝 0))
    (hmargin : (1 / 3 : ℝ) / beta + margin < uInterior) :
    ∀ᶠ n : ℕ in atTop,
      ((width n / 3 + (2 / 3 : ℝ) *
          (2 * drift * (blockLength n : ℝ) / width n ^ 2)) /
          (width n -
            2 * drift * (blockLength n : ℝ) / width n ^ 2)) /
        beta + margin ≤ uInterior := by
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
  simpa only [loss] using
    eventually_staircaseInteriorLowerMargin hbeta hwidth hloss hmargin

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

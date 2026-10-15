/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Setup.Schedule
/-!
# Horizontal sub-tubes of a linearly rising tube

The public objects and theorems in this file are:

- `staircaseLowerEdge`: $r_{t_{j+1}}$.
- `staircaseTubeWidth`: $D-c|I_j|/D^2$.
- `staircaseLowerEdge_eq_endBoundary` and
  `staircaseLowerEdge_add_staircaseTubeWidth_eq_startUpperBoundary`:
  the horizontal sub-tube is exactly $[r_{t_{j+1}},s_{t_j}]$.
- `staircaseTubeWidth_pos_of_stepCost_lt_cube`:
  $c|I_j|<D^3$ gives its positive width.
- `staircaseTubeWidth_pos_of_schedule_bound`:
  the common bound in Wang Yiyang's Lemma 3.5 $2c\ell<D^3$ makes every scheduled
  horizontal sub-tube nonempty.
- `staircaseTubeWidth_le_globalWidth`:
  for $c\ge0$, every horizontal width is at most $D$.
- `staircaseTubeWidth_ge_half_of_schedule_bound`:
  $4c\ell\le D^3$ makes every horizontal width at least $D/2$.
- `staircaseTubeWidth_ge_commonLossBound`:
  for every actual block, $\Delta(j)\ge D-2c\ell/D^2$.

These are the horizontal sub-tubes $H_j$ in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Lower edge of the horizontal sub-tube in one staircase block. -/
noncomputable def staircaseLowerEdge (base drift width : ℝ)
    (start : ℕ → ℕ) (j : ℕ) : ℝ :=
  base + drift * (start (j + 1) : ℝ) / width ^ 2

/-- Width of the horizontal sub-tube during one block. -/
noncomputable def staircaseTubeWidth (width drift : ℝ)
    (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  width - drift * (length j : ℝ) / width ^ 2

/-- The block's lower horizontal edge is the rising lower boundary at its
ending time. -/
theorem staircaseLowerEdge_eq_endBoundary
    (base drift width : ℝ) (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (j : ℕ) :
    staircaseLowerEdge base drift width start j =
      base + drift * ((start j + length j : ℕ) : ℝ) / width ^ 2 := by
  rw [staircaseLowerEdge, hnext j]

/-- The block's upper horizontal edge is the rising upper boundary at its
starting time. -/
theorem staircaseLowerEdge_add_staircaseTubeWidth_eq_startUpperBoundary
    (base drift width : ℝ) (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (j : ℕ) :
    staircaseLowerEdge base drift width start j +
        staircaseTubeWidth width drift length j =
      base + drift * (start j : ℝ) / width ^ 2 + width := by
  rw [staircaseLowerEdge_eq_endBoundary base drift width start length hnext j]
  unfold staircaseTubeWidth
  push_cast
  ring

/-- A staircase sub-tube has positive width when the drift during the
block is smaller than the cubic width scale. -/
theorem staircaseTubeWidth_pos_of_stepCost_lt_cube
    {width drift : ℝ} {length : ℕ → ℕ} {j : ℕ}
    (hwidth : 0 < width)
    (hcost : drift * (length j : ℝ) < width ^ 3) :
    0 < staircaseTubeWidth width drift length j := by
  unfold staircaseTubeWidth
  apply sub_pos.mpr
  apply (div_lt_iff₀ (sq_pos_of_pos hwidth)).2
  nlinarith [hcost]

/-- One upper bound on the common block length ensures positive tube width
for every actual block, including the longer final block. -/
theorem staircaseTubeWidth_pos_of_schedule_bound
    {entrance horizon blockLength : ℕ}
    {width drift : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hcost : 2 * drift * (blockLength : ℝ) < width ^ 3)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    0 < staircaseTubeWidth width drift
      (staircaseBlockLength entrance horizon blockLength) j := by
  have hlength := (staircaseBlockLength_bounds
    hentrance hblockLength hj).2
  have hlengthReal :
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        2 * (blockLength : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hlength)
  have hmul : drift *
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        drift * (2 * (blockLength : ℝ)) :=
    mul_le_mul_of_nonneg_left hlengthReal hdrift
  apply staircaseTubeWidth_pos_of_stepCost_lt_cube hwidth
  nlinarith [hmul, hcost]

/-- Nonnegative drift narrows each horizontal block relative to the global
tilted tube. -/
theorem staircaseTubeWidth_le_globalWidth
    {width drift : ℝ} {length : ℕ → ℕ} {j : ℕ}
    (hdrift : 0 ≤ drift) :
    staircaseTubeWidth width drift length j ≤ width := by
  unfold staircaseTubeWidth
  have hnonneg : 0 ≤ drift * (length j : ℝ) / width ^ 2 := by positivity
  linarith

/-- A common bound on the block length makes all horizontal widths at
least half of the global tilted-tube width. -/
theorem staircaseTubeWidth_ge_half_of_schedule_bound
    {entrance horizon blockLength : ℕ}
    {width drift : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hcost : 4 * drift * (blockLength : ℝ) ≤ width ^ 3)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    width / 2 ≤ staircaseTubeWidth width drift
      (staircaseBlockLength entrance horizon blockLength) j := by
  have hlength := (staircaseBlockLength_bounds
    hentrance hblockLength hj).2
  have hlengthReal :
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        2 * (blockLength : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hlength)
  have hmul : drift *
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        drift * (2 * (blockLength : ℝ)) :=
    mul_le_mul_of_nonneg_left hlengthReal hdrift
  have hsq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hquot : drift *
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) /
        width ^ 2 ≤ width / 2 := by
    apply (div_le_iff₀ hsq).2
    nlinarith [hmul, hcost]
  unfold staircaseTubeWidth
  linarith

/-- The longest scheduled block loses at most two common block lengths of
vertical drift from the global width. -/
theorem staircaseTubeWidth_ge_commonLossBound
    {entrance horizon blockLength : ℕ}
    {width drift : ℝ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    {j : ℕ}
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    width - 2 * drift * (blockLength : ℝ) / width ^ 2 ≤
      staircaseTubeWidth width drift
        (staircaseBlockLength entrance horizon blockLength) j := by
  have hlength := (staircaseBlockLength_bounds
    hentrance hblockLength hj).2
  have hlengthReal :
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        2 * (blockLength : ℝ) := by
    exact_mod_cast (Nat.le_of_lt hlength)
  have hmul : drift *
      ((staircaseBlockLength entrance horizon blockLength j : ℕ) : ℝ) ≤
        2 * drift * (blockLength : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hlengthReal hdrift]
  have hquot := div_le_div_of_nonneg_right hmul
    (sq_pos_of_pos hwidth).le
  unfold staircaseTubeWidth
  linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

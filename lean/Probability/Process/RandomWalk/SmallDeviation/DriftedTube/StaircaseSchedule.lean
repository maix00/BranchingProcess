/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BlockExponent

/-!
# Finite staircase schedule with a longer last block

The public objects and theorems in this file are:

- `staircaseBlockCount`: $q=\lfloor(L-t_1)/\ell\rfloor$.
- `staircaseBlockStart`: $t_k=t_1+k\ell$ for $k<q$ and $t_q=L$.
- `staircaseBlockLength`: $|I_k|=t_{k+1}-t_k$.
- `staircaseBlockStart_zero` and `staircaseBlockStart_count`:
  the first and last block boundaries are $t_1$ and $L$.
- `staircaseBlockStart_mono_succ` and
  `staircaseBlockStart_next_eq_add_length`:
  consecutive block times are ordered and differ by their block length.
- `staircaseBlockLength_interior`:
  every nonfinal block has length $\ell$.
- `staircaseBlockLength_last` and `staircaseBlockLength_last_bounds`:
  the final block has length $\ell+(L-t_1)\bmod\ell$,
  hence lies in $[\ell,2\ell)$.
- `staircaseBlockCount_pos_of_entrance_add_blockLength_le`:
  $L\ge t_1+\ell$ guarantees at least one block.
- `staircaseBlockLength_bounds`:
  every actual block has length in $[\ell,2\ell)$.

These are the discrete schedule definitions in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Number of horizontal blocks after the entrance stage. -/
def staircaseBlockCount (entrance horizon blockLength : ℕ) : ℕ :=
  (horizon - entrance) / blockLength

/-- The first `q` block starts are equally spaced; the final boundary is
the prescribed horizon. -/
def staircaseBlockStart (entrance horizon blockLength : ℕ) (j : ℕ) : ℕ :=
  if j < staircaseBlockCount entrance horizon blockLength then
    entrance + j * blockLength else horizon

/-- The length of one block, including the potentially longer last one. -/
def staircaseBlockLength (entrance horizon blockLength : ℕ)
    (j : ℕ) : ℕ :=
  staircaseBlockStart entrance horizon blockLength (j + 1) -
    staircaseBlockStart entrance horizon blockLength j

/-- A positive block count makes the first block begin at the entrance
time. -/
theorem staircaseBlockStart_zero
    {entrance horizon blockLength : ℕ}
    (hcount : 0 < staircaseBlockCount entrance horizon blockLength) :
    staircaseBlockStart entrance horizon blockLength 0 = entrance := by
  simp [staircaseBlockStart, hcount]

/-- The last block ends at the prescribed horizon. -/
theorem staircaseBlockStart_count
    (entrance horizon blockLength : ℕ) :
    staircaseBlockStart entrance horizon blockLength
      (staircaseBlockCount entrance horizon blockLength) = horizon := by
  simp [staircaseBlockStart]

/-- Every block boundary through the last one is at most the horizon. -/
theorem staircaseBlockStart_le_horizon
    {entrance horizon blockLength : ℕ}
    (hentrance : entrance ≤ horizon)
    {j : ℕ}
    (hj : j ≤ staircaseBlockCount entrance horizon blockLength) :
    staircaseBlockStart entrance horizon blockLength j ≤ horizon := by
  have hq : staircaseBlockCount entrance horizon blockLength *
      blockLength ≤ horizon - entrance := by
    exact Nat.div_mul_le_self _ _
  by_cases hjq : j < staircaseBlockCount entrance horizon blockLength
  · have hjmul : j * blockLength ≤
        staircaseBlockCount entrance horizon blockLength * blockLength :=
      Nat.mul_le_mul_right blockLength hj
    simp only [staircaseBlockStart, hjq, ↓reduceIte]
    omega
  · simp [staircaseBlockStart, hjq]

/-- The staircase block boundaries are ordered. -/
theorem staircaseBlockStart_mono_succ
    {entrance horizon blockLength : ℕ}
    (hentrance : entrance ≤ horizon)
    (j : ℕ) :
    staircaseBlockStart entrance horizon blockLength j ≤
      staircaseBlockStart entrance horizon blockLength (j + 1) := by
  by_cases hj : j < staircaseBlockCount entrance horizon blockLength
  · by_cases hjNext : j + 1 < staircaseBlockCount entrance horizon blockLength
    · simp [staircaseBlockStart, hj, hjNext]
      exact Nat.mul_le_mul_right blockLength (Nat.le_succ j)
    · have hjq : j ≤ staircaseBlockCount entrance horizon blockLength :=
        Nat.le_of_lt hj
      have hbound := staircaseBlockStart_le_horizon hentrance hjq
      simpa [staircaseBlockStart, hjNext] using hbound
  · have hjNext : ¬j + 1 <
        staircaseBlockCount entrance horizon blockLength := by omega
    simp [staircaseBlockStart, hj, hjNext]

/-- Every successor block boundary is the previous one plus that block's
length. -/
theorem staircaseBlockStart_next_eq_add_length
    {entrance horizon blockLength : ℕ}
    (hentrance : entrance ≤ horizon)
    (j : ℕ) :
    staircaseBlockStart entrance horizon blockLength (j + 1) =
      staircaseBlockStart entrance horizon blockLength j +
        staircaseBlockLength entrance horizon blockLength j := by
  unfold staircaseBlockLength
  exact (Nat.add_sub_of_le
    (staircaseBlockStart_mono_succ hentrance j)).symm

/-- Every block before the last one has the common length $\ell$. -/
theorem staircaseBlockLength_interior
    {entrance horizon blockLength j : ℕ}
    (hj : j + 1 < staircaseBlockCount entrance horizon blockLength) :
    staircaseBlockLength entrance horizon blockLength j = blockLength := by
  have hj' : j < staircaseBlockCount entrance horizon blockLength := by omega
  simp only [staircaseBlockLength, staircaseBlockStart,
    hj, hj', ↓reduceIte]
  rw [Nat.succ_mul]
  omega

/-- The last block is one full block plus the remainder of the division
of the post-entrance horizon by the common block length. -/
theorem staircaseBlockLength_last
    {entrance horizon blockLength : ℕ}
    (hentrance : entrance ≤ horizon)
    (hcount : 0 < staircaseBlockCount entrance horizon blockLength) :
    staircaseBlockLength entrance horizon blockLength
      (staircaseBlockCount entrance horizon blockLength - 1) =
      blockLength + (horizon - entrance) % blockLength := by
  let q := staircaseBlockCount entrance horizon blockLength
  have hlast : q - 1 < q := by omega
  have hlastNext : q - 1 + 1 = q := by omega
  have hstartLast : staircaseBlockStart entrance horizon blockLength
      (q - 1) = entrance + (q - 1) * blockLength := by
    simp [staircaseBlockStart, hlast, q]
  have hstartFinish : staircaseBlockStart entrance horizon blockLength
      ((q - 1) + 1) = horizon := by
    rw [hlastNext]
    exact staircaseBlockStart_count entrance horizon blockLength
  have hsplit : q * blockLength =
      (q - 1) * blockLength + blockLength := by
    have hq : q = (q - 1) + 1 := by omega
    calc
      q * blockLength = ((q - 1) + 1) * blockLength :=
        congrArg (· * blockLength) hq
      _ = (q - 1) * blockLength + blockLength := by ring
  have hdivision :
      (horizon - entrance) % blockLength + q * blockLength =
        horizon - entrance := by
    simpa [q, staircaseBlockCount, Nat.mul_comm] using
      (Nat.mod_add_div (horizon - entrance) blockLength)
  have hsum : entrance + (horizon - entrance) = horizon :=
    Nat.add_sub_of_le hentrance
  unfold staircaseBlockLength
  rw [hstartFinish, hstartLast]
  omega

/-- The last horizontal segment has length at least one full block and
strictly less than two common block lengths. -/
theorem staircaseBlockLength_last_bounds
    {entrance horizon blockLength : ℕ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hcount : 0 < staircaseBlockCount entrance horizon blockLength) :
    blockLength ≤ staircaseBlockLength entrance horizon blockLength
        (staircaseBlockCount entrance horizon blockLength - 1) ∧
      staircaseBlockLength entrance horizon blockLength
        (staircaseBlockCount entrance horizon blockLength - 1) <
          2 * blockLength := by
  rw [staircaseBlockLength_last hentrance hcount]
  have hrem := Nat.mod_lt (horizon - entrance) hblockLength
  omega

/-- There is at least one horizontal block when the remaining horizon
contains a full common block length. -/
theorem staircaseBlockCount_pos_of_entrance_add_blockLength_le
    {entrance horizon blockLength : ℕ}
    (hblockLength : 0 < blockLength)
    (hremaining : entrance + blockLength ≤ horizon) :
    0 < staircaseBlockCount entrance horizon blockLength := by
  unfold staircaseBlockCount
  apply Nat.div_pos
  all_goals omega

/-- Every block in the finite schedule has length between one and two
common block lengths. -/
theorem staircaseBlockLength_bounds
    {entrance horizon blockLength j : ℕ}
    (hentrance : entrance ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hj : j < staircaseBlockCount entrance horizon blockLength) :
    blockLength ≤ staircaseBlockLength entrance horizon blockLength j ∧
      staircaseBlockLength entrance horizon blockLength j <
        2 * blockLength := by
  by_cases hbefore : j + 1 <
      staircaseBlockCount entrance horizon blockLength
  · rw [staircaseBlockLength_interior hbefore]
    omega
  · have hlast : j = staircaseBlockCount entrance horizon blockLength - 1 := by
      omega
    rw [hlast]
    exact staircaseBlockLength_last_bounds hentrance hblockLength
      (by omega)

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Tail-merged finite block partitions

For an interval from `start` to `horizon` and a nominal block length
`blockLength`, this module defines the schedule
\[
q=\left\lfloor\frac{\text{horizon}-\text{start}}{\text{blockLength}}\right\rfloor,
\qquad
t_j=\begin{cases}
\text{start}+j\,\text{blockLength},&j<q,\\
\text{horizon},&q\le j.
\end{cases}
\]
The resulting final block absorbs the remainder, so when `q > 0` its length
is `blockLength + (horizon - start) % blockLength`. The construction depends
only on natural-number interval data and can be used independently of any
probability estimate.

The public definitions are:

- `ProbabilityTheory.RandomWalk.tailMergedBlockCount`: the quotient `q`.
- `ProbabilityTheory.RandomWalk.tailMergedBlockStart`: the scheduled boundary
  `t_j`.
- `ProbabilityTheory.RandomWalk.tailMergedBlockLength`: the difference
  between consecutive boundaries.
- `ProbabilityTheory.RandomWalk.tailMergedBlockStart_zero`,
  `tailMergedBlockStart_count`, `tailMergedBlockStart_le_horizon`, and
  `tailMergedBlockStart_mono_succ`: bounds on the schedule's endpoints.
- `ProbabilityTheory.RandomWalk.tailMergedBlockLength_interior`,
  `tailMergedBlockLength_last`, `tailMergedBlockLength_last_bounds`, and
  `tailMergedBlockLength_bounds`: lengths of its ordinary and final blocks.
- `ProbabilityTheory.RandomWalk.tailMergedBlockCount_pos_of_start_add_blockLength_le`:
  positivity of the block count when one full block fits.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Number of nominal blocks before the final block absorbs the remainder. -/
def tailMergedBlockCount (start horizon blockLength : ℕ) : ℕ :=
  (horizon - start) / blockLength

/-- The first `q` block boundaries are equally spaced; the final boundary is
the prescribed horizon. -/
def tailMergedBlockStart (start horizon blockLength : ℕ) (j : ℕ) : ℕ :=
  if j < tailMergedBlockCount start horizon blockLength then
    start + j * blockLength else horizon

/-- The length of one scheduled block, including the potentially longer last
block. -/
def tailMergedBlockLength (start horizon blockLength : ℕ)
    (j : ℕ) : ℕ :=
  tailMergedBlockStart start horizon blockLength (j + 1) -
    tailMergedBlockStart start horizon blockLength j

/-- A positive block count makes the first block begin at `start`. -/
theorem tailMergedBlockStart_zero
    {start horizon blockLength : ℕ}
    (hcount : 0 < tailMergedBlockCount start horizon blockLength) :
    tailMergedBlockStart start horizon blockLength 0 = start := by
  simp [tailMergedBlockStart, hcount]

/-- The last block ends at the prescribed horizon. -/
theorem tailMergedBlockStart_count
    (start horizon blockLength : ℕ) :
    tailMergedBlockStart start horizon blockLength
      (tailMergedBlockCount start horizon blockLength) = horizon := by
  simp [tailMergedBlockStart]

/-- Every scheduled boundary through the last one is at most the horizon. -/
theorem tailMergedBlockStart_le_horizon
    {start horizon blockLength : ℕ}
    (hstart : start ≤ horizon)
    {j : ℕ}
    (hj : j ≤ tailMergedBlockCount start horizon blockLength) :
    tailMergedBlockStart start horizon blockLength j ≤ horizon := by
  have hq : tailMergedBlockCount start horizon blockLength *
      blockLength ≤ horizon - start := by
    exact Nat.div_mul_le_self _ _
  by_cases hjq : j < tailMergedBlockCount start horizon blockLength
  · have hjmul : j * blockLength ≤
        tailMergedBlockCount start horizon blockLength * blockLength :=
      Nat.mul_le_mul_right blockLength hj
    simp only [tailMergedBlockStart, hjq, ↓reduceIte]
    omega
  · simp [tailMergedBlockStart, hjq]

/-- Consecutive scheduled boundaries are ordered. -/
theorem tailMergedBlockStart_mono_succ
    {start horizon blockLength : ℕ}
    (hstart : start ≤ horizon)
    (j : ℕ) :
    tailMergedBlockStart start horizon blockLength j ≤
      tailMergedBlockStart start horizon blockLength (j + 1) := by
  by_cases hj : j < tailMergedBlockCount start horizon blockLength
  · by_cases hjNext : j + 1 < tailMergedBlockCount start horizon blockLength
    · simp [tailMergedBlockStart, hj, hjNext]
      exact Nat.mul_le_mul_right blockLength (Nat.le_succ j)
    · have hjq : j ≤ tailMergedBlockCount start horizon blockLength :=
        Nat.le_of_lt hj
      have hbound := tailMergedBlockStart_le_horizon hstart hjq
      simpa [tailMergedBlockStart, hjNext] using hbound
  · have hjNext : ¬j + 1 <
        tailMergedBlockCount start horizon blockLength := by omega
    simp [tailMergedBlockStart, hj, hjNext]

/-- Each successor boundary equals its predecessor plus that block's length. -/
theorem tailMergedBlockStart_next_eq_add_length
    {start horizon blockLength : ℕ}
    (hstart : start ≤ horizon)
    (j : ℕ) :
    tailMergedBlockStart start horizon blockLength (j + 1) =
      tailMergedBlockStart start horizon blockLength j +
        tailMergedBlockLength start horizon blockLength j := by
  unfold tailMergedBlockLength
  exact (Nat.add_sub_of_le
    (tailMergedBlockStart_mono_succ hstart j)).symm

/-- Every block before the last one has the common nominal length. -/
theorem tailMergedBlockLength_interior
    {start horizon blockLength j : ℕ}
    (hj : j + 1 < tailMergedBlockCount start horizon blockLength) :
    tailMergedBlockLength start horizon blockLength j = blockLength := by
  have hj' : j < tailMergedBlockCount start horizon blockLength := by omega
  simp only [tailMergedBlockLength, tailMergedBlockStart,
    hj, hj', ↓reduceIte]
  rw [Nat.succ_mul]
  omega

/-- The last block absorbs the remainder after the nominal full blocks. -/
theorem tailMergedBlockLength_last
    {start horizon blockLength : ℕ}
    (hstart : start ≤ horizon)
    (hcount : 0 < tailMergedBlockCount start horizon blockLength) :
    tailMergedBlockLength start horizon blockLength
      (tailMergedBlockCount start horizon blockLength - 1) =
      blockLength + (horizon - start) % blockLength := by
  let q := tailMergedBlockCount start horizon blockLength
  have hlast : q - 1 < q := by omega
  have hlastNext : q - 1 + 1 = q := by omega
  have hstartLast : tailMergedBlockStart start horizon blockLength
      (q - 1) = start + (q - 1) * blockLength := by
    simp [tailMergedBlockStart, hlast, q]
  have hstartFinish : tailMergedBlockStart start horizon blockLength
      ((q - 1) + 1) = horizon := by
    rw [hlastNext]
    exact tailMergedBlockStart_count start horizon blockLength
  have hsplit : q * blockLength =
      (q - 1) * blockLength + blockLength := by
    have hq : q = (q - 1) + 1 := by omega
    calc
      q * blockLength = ((q - 1) + 1) * blockLength :=
        congrArg (· * blockLength) hq
      _ = (q - 1) * blockLength + blockLength := by ring
  have hdivision :
      (horizon - start) % blockLength + q * blockLength =
        horizon - start := by
    simpa [q, tailMergedBlockCount, Nat.mul_comm] using
      (Nat.mod_add_div (horizon - start) blockLength)
  have hsum : start + (horizon - start) = horizon :=
    Nat.add_sub_of_le hstart
  unfold tailMergedBlockLength
  rw [hstartFinish, hstartLast]
  omega

/-- The final block has length in `[blockLength, 2 * blockLength)`. -/
theorem tailMergedBlockLength_last_bounds
    {start horizon blockLength : ℕ}
    (hstart : start ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hcount : 0 < tailMergedBlockCount start horizon blockLength) :
    blockLength ≤ tailMergedBlockLength start horizon blockLength
        (tailMergedBlockCount start horizon blockLength - 1) ∧
      tailMergedBlockLength start horizon blockLength
        (tailMergedBlockCount start horizon blockLength - 1) <
          2 * blockLength := by
  rw [tailMergedBlockLength_last hstart hcount]
  have hrem := Nat.mod_lt (horizon - start) hblockLength
  omega

/-- An interval containing one full nominal block has a positive block count. -/
theorem tailMergedBlockCount_pos_of_start_add_blockLength_le
    {start horizon blockLength : ℕ}
    (hblockLength : 0 < blockLength)
    (hremaining : start + blockLength ≤ horizon) :
    0 < tailMergedBlockCount start horizon blockLength := by
  unfold tailMergedBlockCount
  apply Nat.div_pos
  all_goals omega

/-- Every block in the schedule has length in `[blockLength, 2 * blockLength)`. -/
theorem tailMergedBlockLength_bounds
    {start horizon blockLength j : ℕ}
    (hstart : start ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hj : j < tailMergedBlockCount start horizon blockLength) :
    blockLength ≤ tailMergedBlockLength start horizon blockLength j ∧
      tailMergedBlockLength start horizon blockLength j < 2 * blockLength := by
  by_cases hbefore : j + 1 <
      tailMergedBlockCount start horizon blockLength
  · rw [tailMergedBlockLength_interior hbefore]
    omega
  · have hlast : j = tailMergedBlockCount start horizon blockLength - 1 := by
      omega
    rw [hlast]
    exact tailMergedBlockLength_last_bounds hstart hblockLength
      (by omega)

end ProbabilityTheory.RandomWalk

end

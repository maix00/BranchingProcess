/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Finite staircase schedule

The public definitions in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBlockCount`:
  $q=\lfloor(L-t_1)/\ell\rfloor$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBlockStart`:
  $t_k=t_1+k\ell$ for $k<q$ and $t_q=L$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseBlockLength`:
  $|I_k|=t_{k+1}-t_k$.

This finite partition is used in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma
3.5. Its definitions apply to any natural-number entrance time, horizon, and
common block length.
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

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

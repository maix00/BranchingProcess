/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.StaircaseEvent

/-!
# Covering the times after the entrance stage by staircase blocks

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_staircaseBlock_covering_time`:
  if $t_0<j\le t_q$, then one index $k<q$ satisfies
  $t_k<j\le t_{k+1}$.

This is the finite time partition used between the entrance and the last
staircase block in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Every time after the entrance stage and through the final block end
belongs to one of the consecutive block intervals. -/
theorem exists_staircaseBlock_covering_time
    (start : ℕ → ℕ) {q time : ℕ}
    (hentrance : start 0 < time) (hfinish : time ≤ start q) :
    ∃ j : ℕ, j < q ∧ start j < time ∧ time ≤ start (j + 1) := by
  induction q with
  | zero => omega
  | succ q ih =>
      by_cases hbefore : time ≤ start q
      · obtain ⟨j, hj, hleft, hright⟩ := ih hbefore
        exact ⟨j, Nat.lt_succ_of_lt hj, hleft, hright⟩
      · exact ⟨q, Nat.lt_succ_self q, by omega, hfinish⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

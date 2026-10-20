/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.MovingCorridor

/-!
# Robust moving-corridor event

The public definition in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.robustMovingTransitionEvent`:
  $\mathcal R_{n,\Delta,c}(x)=\{\xi:h_j\le x+S_j\le\Delta+h_j\ (1\le j\le n),\
  x+S_n\in[h_n+2\Delta/5,h_n+3\Delta/5]\}$, where
  $S_j=\sum_{i=0}^{j-1}\xi_i$ and $h_j=cj/\Delta^2$.

The central terminal interval is the first-block window used in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The moving entrance corridor with terminal interval
`[hₙ + 2Δ/5, hₙ + 3Δ/5]`. -/
def robustMovingTransitionEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  movingCorridorEvent n width drift start ∩
    {increment |
      drift * (n : ℝ) / width ^ 2 + 2 * width / 5 ≤
        start + AdditivePath.displacement n increment ∧
      start + AdditivePath.displacement n increment ≤
        drift * (n : ℝ) / width ^ 2 + 3 * width / 5}

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end

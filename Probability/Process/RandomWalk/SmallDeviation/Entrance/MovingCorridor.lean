/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Mathlib.Basic.Real.Basic
/-!
# Moving-boundary entrance corridors

## Public declarations

The public declaration in this file is:

For increments $\xi=(\xi_i)_{i\ge0}$, put $S_j=\sum_{i=0}^{j-1}\xi_i$.

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.movingCorridorEvent`:
  the paths satisfying $cj/\Delta^2\le x+S_j\le\Delta+cj/\Delta^2$
  for every $1\le j\le n$.
The moving corridor is the path event used in Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (master's thesis,
Fudan University, 2026), Appendix A.2, Lemma A.7, used in Chapter 3,
Lemma 3.5. Terminal-window restrictions are specified by the corresponding
entrance events.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The finite moving-boundary corridor with no terminal-window restriction. -/
def movingCorridorEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  {increment |
    ∀ k : Fin n,
      drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤
        start + AdditivePath.displacement (k + 1) increment ∧
      start + AdditivePath.displacement (k + 1) increment ≤
        width + drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2}

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end

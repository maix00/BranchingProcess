/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Algebra.BigOperators.AdditivePath.Basic

/-!
# Finite interior entrance event

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance.finiteInteriorEvent`:
  for a starting point $x$, drift $c$, width $\Delta$, and horizon $n$, the
  increments satisfy $c\le x+S_j\le\Delta$ for $1\le j\le n$ and
  $x+S_n\in[5\Delta/12,7\Delta/12]$.

This is the finite event in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Appendix A.2, Lemma A.7.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance

/-- The finite random-walk event used for starts in the middle twelfths
of the entrance corridor. -/
def finiteInteriorEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  {increment |
    (∀ k : Fin n,
      drift ≤ start + AdditivePath.displacement (k + 1) increment ∧
      start + AdditivePath.displacement (k + 1) increment ≤ width) ∧
    5 / 12 * width ≤ start + AdditivePath.displacement n increment ∧
    start + AdditivePath.displacement n increment ≤ 7 / 12 * width}

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.FiniteVariance

end

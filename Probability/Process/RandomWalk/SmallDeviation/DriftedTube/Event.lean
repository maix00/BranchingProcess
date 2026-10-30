/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic

/-!
# Events for linearly tilted random-walk tubes

## Public declarations

The public definition in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEvent`: for
  $L\in\mathbb N$, width $\Delta$, drift $c$, and initial position $r_0$,
  with $Y_j=\sum_{i=0}^{j-1}\xi_i$, the event that
  $r_0+cj/\Delta^2\le Y_j\le r_0+cj/\Delta^2+\Delta$ for $1\le j\le L$.
This is the tilted-tube event used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.4.
-/

open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk

/-- The path event for a linearly rising tube of width `width`, corresponding
to the tilted-tube event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.4. -/
def driftedTubeEvent (horizon : ℕ) (width drift lower : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width}

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

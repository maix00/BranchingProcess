/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic

/-!
# Tilted-tube endpoint event

## Public declarations

The public definition in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEndpointWindowEvent`:
  for $Y_j=\sum_{i=0}^{j-1}\xi_i$ and
  $R_j=r+cj/\Delta^2$, the event
  $\{R_j\le Y_j\le R_j+\Delta\ (1\le j\le L),\;
  Y_L\in[R_L,R_L+v\Delta]\}$.

This is the lower-endpoint event in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 3, Lemma 3.5.
-/

@[expose] public section

open ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- A linearly moving tube with a terminal interval measured from its lower edge. -/
def driftedTubeEndpointWindowEvent
    (horizon : ℕ) (width drift base endpointFraction : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | (∀ j : ℕ, 1 ≤ j → j ≤ horizon →
      base + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        base + drift * (j : ℝ) / width ^ 2 + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2)
        (base + drift * (horizon : ℝ) / width ^ 2 +
          endpointFraction * width)}

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

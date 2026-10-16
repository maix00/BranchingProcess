/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic

/-!
# Tilted-tube endpoint event

The public definition in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEndpointWindowEvent`:
  the linearly moving tube with a terminal window measured from its lower edge.

This event is used in Wang Yiyang, *Asymptotic speed of the $N$-branching random
walk with infinite offspring*, Chapter 3, Lemma 3.5.
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

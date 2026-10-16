/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Event.Drawdown
public import Algebra.BigOperators.AdditivePath

/-!
# Drawdown and endpoint event for an increment sequence

The public definition `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent` is
$B_{L,\Delta,r}=\{\xi:S_i-S_j\le\Delta\ (0\le i\le j\le L),\ S_L\le r\}$,
where $S_j$ is the partial sum of the increments. This event is shared by
the finite-variance upper estimate and branching-random-walk applications.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- A finite-horizon event imposing both a drawdown bound and an endpoint
upper bound. -/
def noLargeDropEndpointBelowEvent (horizon : ℕ) (delta threshold : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | (∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta) ∧
    AdditivePath.displacement horizon increment ≤ threshold}

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

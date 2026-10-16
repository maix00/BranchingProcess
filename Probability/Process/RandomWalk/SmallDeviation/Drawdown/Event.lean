/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Event.Drawdown
public import Algebra.BigOperators.AdditivePath.Basic

/-!
# Drawdown and endpoint event for an increment sequence

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent`:
  $B_{L,\Delta,r}=\{\xi:S_i-S_j\le\Delta\ (0\le i\le j\le L),\ S_L\le r\}$,
  where $S_j$ is the partial sum of the increments.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_le_threshold_add_delta_of_noLargeDrop`:
  if $S_i-S_j\le\Delta$ for $0\le i\le j\le L$ and $S_L\le r$, then
  $S_i\le r+\Delta$ for every $0\le i\le L$.

This event is shared by the finite-variance upper estimate and
branching-random-walk applications. The endpoint implication is a deterministic
consequence of the drawdown condition.
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

/-- A path with bounded drawdown and a bounded endpoint stays below the
endpoint threshold plus one drawdown allowance throughout the finite horizon.
-/
theorem additivePath_le_threshold_add_delta_of_noLargeDrop
    {horizon : ℕ} (increment : ℕ → ℝ) (delta threshold : ℝ)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    (hendpoint : AdditivePath.displacement horizon increment ≤ threshold) :
    ∀ i ≤ horizon,
      AdditivePath.displacement i increment ≤ threshold + delta := by
  intro i hi
  have h := hnoDrop i horizon hi (Nat.le_refl _)
  linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

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
  where $S_j=\sum_{k=0}^{j-1}\xi_k$ is the partial sum of the increments.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_le_threshold_add_delta_of_noLargeDrop`:
  if $S_i-S_j\le\Delta$ for $0\le i\le j\le L$ and $S_L\le r$, then
  $S_i\le r+\Delta$ for every $0\le i\le L$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_mem_noLargeDropEndpointBelowEvent_of_monotoneCorridor`:
  for nondecreasing $(d_j)_{j=0}^L$, if $d_j\le S_j\le d_j+\Delta$ for every $j$, then
  $S_i-S_j\le\Delta$ for $i\le j$ and $S_L\le d_L+\Delta$.

This event is shared by finite-variance and branching-random-walk estimates.
The endpoint and monotone-corridor implications are deterministic consequences
of the event conditions.
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

/-- A path in a constant-width corridor above a nondecreasing lower boundary
has drawdown at most the corridor width, and its endpoint lies below the
terminal upper boundary. -/
theorem additivePath_mem_noLargeDropEndpointBelowEvent_of_monotoneCorridor
    (horizon : ℕ) (drift : ℕ → ℝ) (width : ℝ)
    (hmonotone : Monotone drift)
    (increment : ℕ → ℝ)
    (hpath : ∀ j : Fin (horizon + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (drift (j : ℕ)) (drift (j : ℕ) + width)) :
    increment ∈
      noLargeDropEndpointBelowEvent horizon width (drift horizon + width) := by
  constructor
  · intro i j hij hj
    have hi := hpath ⟨i, Nat.lt_succ_of_le (hij.trans hj)⟩
    have hj' := hpath ⟨j, Nat.lt_succ_of_le hj⟩
    linarith [hi.2, hj'.1, hmonotone hij]
  · have hend := hpath ⟨horizon, Nat.lt_succ_self horizon⟩
    exact hend.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

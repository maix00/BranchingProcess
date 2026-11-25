/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Affine

/-!
# Events for linearly tilted random-walk tubes

## Public declarations

The public declarations in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEvent`: for
  $L\in\mathbb N$, width $\Delta$, drift $c$, and initial position $r_0$,
  with $Y_j=\sum_{i=0}^{j-1}\xi_i$, the event that
  $r_0+cj/\Delta^2\le Y_j\le r_0+cj/\Delta^2+\Delta$ for $1\le j\le L$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.affineCorridorPrefix_history_subset_driftedTubeEvent`
  gives `historyₙ(x,z)∈prefix(r,c/Δ²,Δ) ⇒ z∈tube(n,Δ,c,r-x)`.
  This deterministic inclusion requires no sign or moment assumptions.

This is the tilted-tube event used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
(Fudan University, 2026), Chapter 3, Lemma 3.4.
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

/-- Forgetting time zero in a finite affine history gives the positive-time
increment tube after translating by the initial position. -/
theorem affineCorridorPrefix_history_subset_driftedTubeEvent
    (n : ℕ) (initial lower c width : ℝ) :
    {increment | history n initial increment ∈
      affineCorridorPrefix n lower (c / width ^ 2) width} ⊆
      driftedTubeEvent n width c (lower - initial) := by
  intro increment h j _ hj
  have hk := h (⟨j, by omega⟩ : Fin (n + 1))
  change lower + (c / width ^ 2) * (j : ℝ) ≤ _ ∧
    _ ≤ lower + (c / width ^ 2) * (j : ℝ) + width at hk
  simp only [history_apply, div_mul_eq_mul_div] at hk
  constructor <;> linarith [hk.1, hk.2]

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

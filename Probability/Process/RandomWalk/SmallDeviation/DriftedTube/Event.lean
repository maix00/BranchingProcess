/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event

/-!
# Events for linearly tilted random-walk tubes

The public objects and theorem in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEvent`: for
  $L\in\mathbb N$, width $\Delta$, drift $c$, and initial position $r_0$,
  with $Y_j=\sum_{i=0}^{j-1}\xi_i$, the event that
  $r_0+cj/\Delta^2\le Y_j\le r_0+cj/\Delta^2+\Delta$ for $1\le j\le L$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEvent_subset_noLargeDropEndpointBelowEvent`: for $c\ge0$ and
  $-\Delta\le r_0\le0$, this tube event implies the no-large-drop event
  with terminal bound $\Delta+cL/\Delta^2$.

These are the event and geometric inclusion used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.4.
-/

open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The path event for a linearly rising tube of width `width`, corresponding
to the tilted-tube event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.4. -/
def driftedTubeEvent (horizon : ℕ) (width drift lower : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width}

/-- On a tube with nonnegative drift, the upper constraint at time `i`
and lower constraint at time `j ≥ i` bound the drawdown by its width. -/
theorem driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
    (horizon : ℕ) {width drift lower : ℝ}
    (hdrift : 0 ≤ drift)
    (hlower : -width ≤ lower) (hupper : lower ≤ 0) :
    driftedTubeEvent horizon width drift lower ⊆
      noLargeDropEndpointBelowEvent horizon width
        (width + drift * (horizon : ℝ) / width ^ 2) := by
  intro increment hpath
  let lowerBoundary : ℕ → ℝ := fun j =>
    lower + drift * (j : ℝ) / width ^ 2
  have hslope : 0 ≤ drift / width ^ 2 := div_nonneg hdrift (sq_nonneg width)
  have hmonotone : Monotone lowerBoundary := by
    intro i j hij
    dsimp [lowerBoundary]
    have htime : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hrate : drift * (i : ℝ) / width ^ 2 ≤
        drift * (j : ℝ) / width ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left htime hslope
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    linarith [hrate]
  have hcorridor : ∀ j : Fin (horizon + 1),
      AdditivePath.displacement (j : ℕ) increment ∈
        Set.Icc (lowerBoundary (j : ℕ))
          (lowerBoundary (j : ℕ) + width) := by
    intro j
    by_cases hjzero : (j : ℕ) = 0
    ·
      have hdisplacement : AdditivePath.displacement (j : ℕ) increment = 0 := by
        rw [hjzero, AdditivePath.displacement_zero]
      have hlowerBoundary : lowerBoundary (j : ℕ) = lower := by
        simp [lowerBoundary, hjzero]
      rw [hdisplacement, hlowerBoundary]
      exact ⟨hupper, by linarith [hlower]⟩
    · have hjpos : 1 ≤ (j : ℕ) := by omega
      have hjbound : (j : ℕ) ≤ horizon := Nat.le_of_lt_succ j.isLt
      have h := hpath (j : ℕ) hjpos hjbound
      simpa [lowerBoundary] using h
  have hdrawdown :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.additivePath_mem_noLargeDropEndpointBelowEvent_of_monotoneCorridor
      horizon lowerBoundary width hmonotone increment hcorridor
  change
    (∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ width) ∧
      AdditivePath.displacement horizon increment ≤
        lowerBoundary horizon + width at hdrawdown
  change
    (∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ width) ∧
      AdditivePath.displacement horizon increment ≤
        width + drift * (horizon : ℝ) / width ^ 2
  refine ⟨hdrawdown.1, ?_⟩
  dsimp [lowerBoundary] at hdrawdown
  linarith [hdrawdown.2, hupper]


end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

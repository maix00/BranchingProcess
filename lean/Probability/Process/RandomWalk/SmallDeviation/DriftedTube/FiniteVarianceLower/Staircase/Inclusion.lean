/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Partition
/-!
# The staircase event lies inside the target tilted tube

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeEndpointWindowEvent`:
  the tilted-tube event through time $L$ with a final endpoint window
  $[r_L,r_L+vD]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.initialInterTubeBlocks_subset_driftedTubeEndpointWindowEvent`:
  if the entrance stays in the target tube, each horizontal block spans
  $[r_{t_{j+1}},s_{t_j}]$, and the last block ends in the final window,
  then the entrance and all successful blocks imply the target event.

This is the deterministic event inclusion at the start and end of the
reverse Markov product in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- A rising tube with a terminal interval measured from its lower edge. -/
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

/-- The entrance and all horizontal staircase blocks imply the full
tilted-tube event and its final endpoint condition. -/
theorem initialInterTubeBlocks_subset_driftedTubeEndpointWindowEvent
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q horizon : ℕ) (hq : 0 < q)
    (hfinish : start q = horizon)
    (initial : Set (ℕ → ℝ))
    (width drift base endpointFraction : ℝ)
    (hdrift : 0 ≤ drift)
    (blockLower blockWidth v₁ v₂ : ℕ → ℝ)
    (hblockLower : ∀ j, j < q →
      blockLower j =
        base + drift * ((start j + length j : ℕ) : ℝ) / width ^ 2)
    (hblockUpper : ∀ j, j < q →
      blockLower j + blockWidth j =
        base + drift * (start j : ℝ) / width ^ 2 + width)
    (hentrance : ∀ increment ∈ initial, ∀ time : ℕ,
      1 ≤ time → time ≤ start 0 →
        base + drift * (time : ℝ) / width ^ 2 ≤
          AdditivePath.displacement time increment ∧
        AdditivePath.displacement time increment ≤
          base + drift * (time : ℝ) / width ^ 2 + width)
    (hfinalWindow :
      Set.Icc
        (blockLower (q - 1) + v₁ (q - 1) * blockWidth (q - 1))
        (blockLower (q - 1) + v₂ (q - 1) * blockWidth (q - 1)) ⊆
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2)
        (base + drift * (horizon : ℝ) / width ^ 2 +
          endpointFraction * width)) :
    initial ∩ conditionalBlockIntersection
      (fun j => tubeBlockEvent (start j) (length j)
        (blockLower j) (blockWidth j) (v₁ j) (v₂ j)) q ⊆
      driftedTubeEndpointWindowEvent
        horizon width drift base endpointFraction := by
  intro increment hin
  rcases hin with ⟨hinitial, hblocks⟩
  constructor
  · intro time htimePos htimeEnd
    by_cases hbefore : time ≤ start 0
    · exact hentrance increment hinitial time htimePos hbefore
    · have hafter : start 0 < time := by omega
      have htimeFinish : time ≤ start q := by simpa [hfinish] using htimeEnd
      obtain ⟨j, hj, hjStart, hjEnd⟩ :=
        exists_staircaseBlock_covering_time start hafter htimeFinish
      have hjBlock : increment ∈
          tubeBlockEvent (start j) (length j)
            (blockLower j) (blockWidth j) (v₁ j) (v₂ j) :=
        (mem_conditionalBlockIntersection_iff _ q increment).mp hblocks j hj
      have hwidthEq : blockWidth j =
          (base + drift * (start j : ℝ) / width ^ 2 + width) -
            (base + drift * ((start j + length j : ℕ) : ℝ) /
              width ^ 2) := by
        have hupper := hblockUpper j hj
        rw [hblockLower j hj] at hupper
        linarith
      have hjBlock' : increment ∈ tubeBlockEvent
          (start j) (length j)
          (base + drift * ((start j + length j : ℕ) : ℝ) / width ^ 2)
          ((base + drift * (start j : ℝ) / width ^ 2 + width) -
            (base + drift * ((start j + length j : ℕ) : ℝ) / width ^ 2))
          (v₁ j) (v₂ j) := by
        rw [hblockLower j hj, hwidthEq] at hjBlock
        exact hjBlock
      apply tubeBlockEvent_mem_driftedTube_at_time hdrift
        (Nat.le_of_lt hjStart) _ hjBlock'
      rw [← hnext j]
      exact hjEnd
  · have hlast : q - 1 < q := by omega
    have hlastEnd : q - 1 + 1 = q := by omega
    have hlastBlock : increment ∈
        tubeBlockEvent (start (q - 1)) (length (q - 1))
          (blockLower (q - 1)) (blockWidth (q - 1))
          (v₁ (q - 1)) (v₂ (q - 1)) :=
      (mem_conditionalBlockIntersection_iff _ q increment).mp hblocks
        (q - 1) hlast
    have hlastPosition := tubeBlockEvent_end_mem hlastBlock
    rw [← hnext (q - 1), hlastEnd, hfinish] at hlastPosition
    exact hfinalWindow hlastPosition

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

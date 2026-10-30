/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Basic.Real.Basic
import Probability.Process.RandomWalk.Path.Block.Partition.Basic

/-!
# Tube events for the finite-variance drawdown proof

## Internal proof declarations

The proof of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring*, Chapter 3, Lemma 3.3 uses these block events:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownTubePairEvent`:
  for a past increment vector $x\in\mathbb R^n$ and a new block
  $y\in\mathbb R^m$, $sum_{i<n}x_i+\sum_{i<k}y_i\in[c(x)-w,c(x)]$
  for every $k\le m$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownTubeBlockEvent`:
  the corresponding subset of infinite increment sequences, obtained by
  taking their prefix and next-block coordinates.

They are used by the conditional-block and jump-pattern steps of that proof.
-/

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The event for a pair consisting of a past increment prefix and the next
block: throughout the block, the walk remains in the interval
`[center(prefix) - width, center(prefix)]`. -/
def drawdownTubePairEvent {start length : ℕ}
    (center : (Fin start → ℝ) → ℝ) (width : ℝ) :
    Set ((Fin start → ℝ) × (Fin length → ℝ)) :=
  {pair | ∀ k : Fin (length + 1),
    (∑ i : Fin start, pair.1 i) + Fin.partialSum pair.2 k ∈
      Set.Icc (center pair.1 - width) (center pair.1)}

/-- The tube event for one increment block, with its center determined by
the increment prefix at the block's starting time. -/
def drawdownTubeBlockEvent (start length : ℕ)
    (center : (Fin start → ℝ) → ℝ) (width : ℝ) : Set (ℕ → ℝ) :=
  {increment |
    (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) ∈
      drawdownTubePairEvent center width}

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end

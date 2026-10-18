/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic

/-!
# Drawdown tube events for increment blocks

The public constructions in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownTubePairEvent`:
  for a past increment vector and a new block, every translated partial sum
  lies in $[c(x)-w,c(x)]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.drawdownTubeBlockEvent`:
  the corresponding event on an infinite increment sequence, obtained from
  its past and block coordinates.

These are the block events used in the discretized-maximum proof of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, Lemma 3.3.
-/

@[expose] public section

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

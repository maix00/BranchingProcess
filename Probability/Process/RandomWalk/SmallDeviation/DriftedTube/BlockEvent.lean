/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Combinatorics.Sequence.Block

/-!
# Finite block events for linearly tilted tubes

The public constructions in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubePairEvent`:
  for a prefix $x\in\mathbb R^s$ and a block $z\in\mathbb R^m$, each combined
  partial sum $\sum_{i<s}x_i+\sum_{i<k}z_i$, $0\le k\le m$, lies in
  $[r+c(s+k)/\Delta^2,r+c(s+k)/\Delta^2+\Delta]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.driftedTubeBlockEvent`:
  the corresponding event on a full increment sequence, using the prefix of
  length `start` and the block of length `length` starting there.

These are the finite-block events in the equal-length decomposition of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3, proof of
Lemma 3.4.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The path event for one tilted-tube block, expressed in terms of the
increments before the block and the increments in the block. At block time
`k`, the global interval is
`[lower + drift * (start + k) / width^2,
  lower + drift * (start + k) / width^2 + width]`. -/
def driftedTubePairEvent {start length : ℕ}
    (lower width drift : ℝ) :
    Set ((Fin start → ℝ) × (Fin length → ℝ)) :=
  {pair | ∀ k : Fin (length + 1),
    lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
        (∑ i : Fin start, pair.1 i) +
          Fin.partialSum pair.2 k ∧
      (∑ i : Fin start, pair.1 i) +
          Fin.partialSum pair.2 k ≤
        lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 + width}

/-- The event that the full increment path remains in the tilted tube over a
block, including both block endpoints. -/
def driftedTubeBlockEvent (start length : ℕ)
    (lower width drift : ℝ) : Set (ℕ → ℝ) :=
  {increment |
    (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) ∈
      driftedTubePairEvent lower width drift}

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

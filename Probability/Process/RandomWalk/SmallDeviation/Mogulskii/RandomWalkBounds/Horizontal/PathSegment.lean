/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.RandomWalkBounds.Horizontal.Basic
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic

/-!
# Segment oscillation and finite increment blocks

The public theorem in this file is
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.blockOscillationEvent_of_additiveSegment`:
if the additive path on the interval $[s,s+\ell]$ has oscillation at most
$w$, then the length-$\ell$ increment block starting at $s$ belongs to the
finite-block oscillation event of width $w$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.RandomWalk

/-- An oscillation bound for the additive path over one segment implies the
finite-block oscillation event for the increments in that segment. -/
lemma blockOscillationEvent_of_additiveSegment
    {start length : ℕ} {increment : ℕ → ℝ} {width : ℝ}
    (hsegment : OscillationBounded
      (fun k : Fin (length + 1) =>
        AdditivePath.displacement (start + (k : ℕ)) increment) width) :
    blockOscillationEvent width length
      (Combinatorics.Sequence.blockCoordinates start length increment) := by
  change OscillationBounded
    (fun k : Fin (length + 1) =>
      Fin.partialSum
        (Combinatorics.Sequence.blockCoordinates start length increment) k)
    width
  intro i j
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) i -
    Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) j| ≤ width
  have hpartial (k : Fin (length + 1)) :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k =
        AdditivePath.displacement (start + (k : ℕ)) increment -
          AdditivePath.displacement start increment := by
    rw [partialSum_blockCoordinates, AdditivePath.displacement_add_eq_add_blockSum]
    ring
  rw [hpartial i, hpartial j]
  calc
    |(AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement start increment) -
      (AdditivePath.displacement (start + (j : ℕ)) increment -
          AdditivePath.displacement start increment)| =
        |AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement (start + (j : ℕ)) increment| := by
      congr 1
      ring
    _ ≤ width := hsegment i j

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end

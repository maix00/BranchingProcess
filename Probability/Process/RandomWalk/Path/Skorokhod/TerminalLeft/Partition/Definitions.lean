/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.StepCorridor

/-!
# Discrete index data for terminal-left partition cells

For the common boundary grid $t_j$, let
$F_n(t)=\lfloor nt\rfloor$ and
$G_n(j)=\min(F_n(t_j),n-1)$. The clipped index records the terminal-left
convention, and the successive differences of $G_n$ give its integer cell
lengths.

These definitions encode the terminal index $n-1$ in A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081.

## Public declarations

- `terminalLeftPartitionKnotIndex` is $G_n(j)$, the clipped index of knot $j$.
- `terminalLeftPartitionCellStepLengths` is $G_n(j+1)-G_n(j)$ on each valid
  cell, extended by zero outside the finite common partition.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor
open Skorokhod.PathClass.StepCorridor

/-- The integer position assigned to a terminal-left partition knot.
Clipping the usual floor index at `n - 1` changes only the terminal knot. -/
noncomputable def terminalLeftPartitionKnotIndex (n : ℕ) (upper lower : StepBoundary)
    (j : ℕ) : ℕ :=
  min (commonPartitionFloorTimeIndex n
    (StepBoundary.commonPartitionGrid upper lower j)) (n - 1)

/-- Terminal-left cell lengths, extended by zero beyond the finite
partition. Their cumulative sums end at `n - 1`. -/
noncomputable def terminalLeftPartitionCellStepLengths (n : ℕ) (upper lower : StepBoundary) :
    ℕ → ℕ := fun j =>
  if _hj : j < (StepBoundary.commonKnots upper lower).card - 1 then
    terminalLeftPartitionKnotIndex n upper lower (j + 1) -
      terminalLeftPartitionKnotIndex n upper lower j
  else 0

end ProbabilityTheory.RandomWalk

end

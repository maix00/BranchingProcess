/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Combinatorics.Sequence.Block
import Probability.Process.RandomWalk.Path.Block.Partition.StepCorridor
import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Definitions
import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary.Partition

/-!
# Proof lemmas for terminal-left partition indices

These lemmas establish the endpoint, monotonicity, cumulative-length, and
terminal-cell identities for the clipped floor index
$G_n(j)=\min(\lfloor nt_j\rfloor,n-1)$. They support the terminal-left path
evaluation and cell-length limit statements in the sibling `Basic` module and
the finite-partition Mogul'skii proofs.

The endpoint convention follows A. A. Mogul'skii, Theorem 3, Section 4,
p. 764, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.

## Internal declarations

- `knotIndex_mono`, `knotIndex_zero`, `knotIndex_last`, and
  `knotIndex_eq_floor_of_lt_last` give the basic order and endpoint formulas
  for $G_n$.
- `cellStepLengths_eq_floorDifference` and `blockStart_cellStepLengths`
  identify the lengths and their cumulative sums.
- `cellStepLength_eq_common_of_not_last` and
  `cellStepLength_eq_common_sub_one_last` identify the ordinary and terminal
  cell lengths.
-/

section

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor
open Skorokhod.PathClass.StepCorridor

namespace ProbabilityTheory.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Lemmas

lemma knotIndex_mono (n : ℕ) (upper lower : StepBoundary)
    {i j : ℕ} (hij : i ≤ j) :
    terminalLeftPartitionKnotIndex n upper lower i ≤
      terminalLeftPartitionKnotIndex n upper lower j := by
  exact min_le_min
    (commonPartitionFloorTimeIndex_mono n
      (StepBoundary.monotone_commonPartitionGrid upper lower hij)) le_rfl

lemma knotIndex_zero (n : ℕ) (upper lower : StepBoundary) :
    terminalLeftPartitionKnotIndex n upper lower 0 = 0 := by
  simp [terminalLeftPartitionKnotIndex, commonPartitionFloorTimeIndex,
    StepBoundary.commonPartitionGrid_zero]

lemma knotIndex_last (n : ℕ) (upper lower : StepBoundary) :
    terminalLeftPartitionKnotIndex n upper lower
      ((StepBoundary.commonKnots upper lower).card - 1) = n - 1 := by
  simp [terminalLeftPartitionKnotIndex, commonPartitionFloorTimeIndex,
    StepBoundary.commonPartitionGrid_last]

lemma knotIndex_eq_floor_of_lt_last
    (n : ℕ) (upper lower : StepBoundary)
    {j : ℕ} (hj : j < (StepBoundary.commonKnots upper lower).card - 1) :
    terminalLeftPartitionKnotIndex n upper lower j =
      commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower j) := by
  apply Nat.min_eq_left
  apply commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top
  have hgrid : StepBoundary.commonPartitionGrid upper lower j < ⊤ := by
    have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower j hj
    have hnext : j + 1 ≤ (StepBoundary.commonKnots upper lower).card - 1 := by
      have hlt := hj
      have hcard : 1 ≤ (StepBoundary.commonKnots upper lower).card := by
        exact Nat.succ_le_iff.mpr
          (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
      omega
    have htail := StepBoundary.monotone_commonPartitionGrid upper lower hnext
    rw [StepBoundary.commonPartitionGrid_last] at htail
    exact lt_of_lt_of_le hstrict htail
  exact hgrid

lemma cellStepLengths_eq_floorDifference
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    terminalLeftPartitionCellStepLengths n upper lower i.val =
      terminalLeftPartitionKnotIndex n upper lower (i.val + 1) -
        terminalLeftPartitionKnotIndex n upper lower i.val := by
  simp [terminalLeftPartitionCellStepLengths, i.isLt]

lemma blockStart_cellStepLengths
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Combinatorics.Sequence.blockStart
        (terminalLeftPartitionCellStepLengths n upper lower) i.val =
      terminalLeftPartitionKnotIndex n upper lower i.val := by
  have hprefix (j : ℕ) (hj : j ≤
      (StepBoundary.commonKnots upper lower).card - 1) :
      Combinatorics.Sequence.blockStart
          (terminalLeftPartitionCellStepLengths n upper lower) j =
        terminalLeftPartitionKnotIndex n upper lower j := by
    induction j with
    | zero =>
        simp [knotIndex_zero]
    | succ j ih =>
        have hjlt : j < (StepBoundary.commonKnots upper lower).card - 1 := by omega
        rw [Combinatorics.Sequence.blockStart_succ, ih (by omega)]
        rw [terminalLeftPartitionCellStepLengths, dite_eq_left hjlt]
        simpa [Nat.succ_eq_add_one] using
          (Nat.add_sub_of_le (knotIndex_mono n upper lower (Nat.le_succ j)))
  exact hprefix i.val (Nat.le_of_lt i.isLt)

lemma cellStepLength_eq_common_of_not_last
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hi : i.val + 1 < (StepBoundary.commonKnots upper lower).card - 1) :
    terminalLeftPartitionCellStepLengths n upper lower i.val =
      commonPartitionCellStepLength n upper lower i := by
  rw [cellStepLengths_eq_floorDifference]
  rw [knotIndex_eq_floor_of_lt_last n upper lower hi,
    knotIndex_eq_floor_of_lt_last n upper lower (by omega)]
  rfl

lemma cellStepLength_eq_common_sub_one_last
    (n : ℕ) (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hi : i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1) :
    terminalLeftPartitionCellStepLengths n upper lower i.val =
      commonPartitionCellStepLength n upper lower i - 1 := by
  rw [cellStepLengths_eq_floorDifference,
    show i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 from hi,
    knotIndex_last]
  have hleft := knotIndex_eq_floor_of_lt_last n upper lower i.isLt
  rw [hleft]
  have htop : commonPartitionFloorTimeIndex n ⊤ = n := by
    simp [commonPartitionFloorTimeIndex]
  have hcommon : commonPartitionCellStepLength n upper lower i =
      n - commonPartitionFloorTimeIndex n
        (StepBoundary.commonPartitionGrid upper lower i.val) := by
    unfold commonPartitionCellStepLength
    rw [show i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 by omega,
      StepBoundary.commonPartitionGrid_last, htop]
  rw [hcommon]
  have hleftle := commonPartitionFloorTimeIndex_le_n_sub_one_of_lt_top n
    (by
      have hleftlt : StepBoundary.commonPartitionGrid upper lower i.val < ⊤ := by
        have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower i.val i.isLt
        rw [hi, StepBoundary.commonPartitionGrid_last] at hstrict
        exact hstrict
      exact hleftlt)
  omega

end ProbabilityTheory.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Lemmas

end

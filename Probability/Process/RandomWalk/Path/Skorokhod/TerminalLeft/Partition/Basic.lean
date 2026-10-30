/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Definitions
public import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
import all Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Lemmas.Index

/-!
# Terminal-left path values on a common partition

Let $t_j$ be the common partition grid, $F_n(t)=\lfloor nt\rfloor$, and
$G_n(j)=\min(F_n(t_j),n-1)$. The terminal-left path records
$S_0,\ldots,S_{n-1}$, so its final knot is indexed by $n-1$. This convention
is used in A. A. Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations
in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081.

## Public declarations

- `terminalLeftNormalizedStepCadlagPathIcc_commonPartitionGrid_apply` gives
  $Y_n^{\mathrm{TL}}(t_j)=s_n^{-1}S_{G_n(j)}$ for $n>0$.
- `tendsto_terminalLeftPartitionCellStepLength_div_nat` gives
  $\ell_i(n)/n\to t_{i+1}-t_i$ for every fixed cell. The last cell has one
  fewer discrete step because its terminal value is $S_{n-1}$.
-/

@[expose] public section

open Filter
open ProbabilityTheory.RandomWalk.Path.Block.Partition.StepCorridor
open ProbabilityTheory.RandomWalk.Path.Skorokhod.TerminalLeft.Partition.Lemmas
open Skorokhod.PathClass.StepCorridor

namespace ProbabilityTheory.RandomWalk

/-- At each terminal-left partition knot, the path records the position
indexed by `terminalLeftPartitionKnotIndex`; at the top this is `S_(n-1)`. -/
theorem terminalLeftNormalizedStepCadlagPathIcc_commonPartitionGrid_apply
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ)
    (upper lower : StepBoundary)
    (j : Fin (StepBoundary.commonKnots upper lower).card) :
    terminalLeftNormalizedStepCadlagPathIcc scale n increment
        (StepBoundary.commonPartitionGrid upper lower j.val) =
      (scale n)⁻¹ * AdditivePath.displacement
        (terminalLeftPartitionKnotIndex n upper lower j.val) increment := by
  by_cases hj : j.val < (StepBoundary.commonKnots upper lower).card - 1
  · have htop : StepBoundary.commonPartitionGrid upper lower j.val ≠ ⊤ := by
      apply ne_of_lt
      have hstrict := StepBoundary.commonPartitionGrid_strictSucc upper lower j.val hj
      have hnext : j.val + 1 ≤ (StepBoundary.commonKnots upper lower).card - 1 := by
        have hcard : 1 ≤ (StepBoundary.commonKnots upper lower).card := by
          exact Nat.succ_le_iff.mpr
            (Finset.card_pos.mpr (StepBoundary.commonKnots_nonempty upper lower))
        omega
      have htail := StepBoundary.monotone_commonPartitionGrid upper lower hnext
      rw [StepBoundary.commonPartitionGrid_last] at htail
      exact lt_of_lt_of_le hstrict htail
    rw [terminalLeftNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment htop,
      knotIndex_eq_floor_of_lt_last n upper lower hj]
    change RandomWalk.normalizedStepPath scale n increment
        (StepBoundary.commonPartitionGrid upper lower j.val : ℝ) = _
    rfl
  · have hjlast : j.val = (StepBoundary.commonKnots upper lower).card - 1 := by omega
    have htop : StepBoundary.commonPartitionGrid upper lower j.val = ⊤ := by
      rw [hjlast, StepBoundary.commonPartitionGrid_last]
    rw [htop, terminalLeftNormalizedStepCadlagPathIcc_apply_top scale hn increment,
      hjlast, knotIndex_last]

/-- The number of terminal-left steps assigned to a common-partition cell,
normalized by the total step count, converges to the cell's time length. -/
theorem tendsto_terminalLeftPartitionCellStepLength_div_nat
    (upper lower : StepBoundary)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    Tendsto
      (fun n => (terminalLeftPartitionCellStepLengths n upper lower i.val : ℝ) /
        (n : ℝ)) atTop
      (nhds ((StepBoundary.commonPartitionGrid upper lower (i.val + 1) : unitInterval) -
        StepBoundary.commonPartitionGrid upper lower i.val)) := by
  have hlastOrNot : i.val + 1 = (StepBoundary.commonKnots upper lower).card - 1 ∨
      i.val + 1 < (StepBoundary.commonKnots upper lower).card - 1 := by omega
  rcases hlastOrNot with hlast | hnotlast
  · have heq : (fun n =>
        (terminalLeftPartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n =>
          ((commonPartitionCellStepLength n upper lower i - 1 : ℕ) : ℝ) /
            (n : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [cellStepLength_eq_common_sub_one_last n upper lower i hlast]
    exact (tendsto_commonPartitionCellRangeHorizon_div_nat upper lower i).congr' heq.symm
  · have heq : (fun n =>
        (terminalLeftPartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ)) =
        fun n => (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ) := by
      funext n
      exact congrArg (fun k : ℕ => (k : ℝ) / (n : ℝ))
        (cellStepLength_eq_common_of_not_last n upper lower i hnotlast)
    have heq' : (fun n => (commonPartitionCellStepLength n upper lower i : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (terminalLeftPartitionCellStepLengths n upper lower i.val : ℝ) / (n : ℝ) :=
      Filter.Eventually.of_forall fun n => (congrFun heq n).symm
    exact (tendsto_commonPartitionCellStepLength_div_nat upper lower i).congr' heq'

end ProbabilityTheory.RandomWalk

end

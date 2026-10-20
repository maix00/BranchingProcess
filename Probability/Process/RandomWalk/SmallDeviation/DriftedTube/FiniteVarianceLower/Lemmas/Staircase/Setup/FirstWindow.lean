/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.SetNotationForOrder
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.BlockTube
public import Probability.Process.RandomWalk.Path.Block.Partition.TailMerged
import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.BlockTube
/-!
# First entrance window of the staircase

The module-visible supporting lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseFirstInteriorWindow`: if $10c\ell<\Delta^3$, the robust
  entrance endpoint interval
  $[r_{t_1}+2\Delta/5,r_{t_1}+3\Delta/5]$ lies inside the central
  window of the first horizontal sub-tube.

This is the first-window geometry in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5. Appendix A.2, Lemma A.7 gives the
probability lower bound for the displayed entrance interval.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- With at least two blocks remaining, the first one has the common
length rather than the extended final length. -/
private lemma staircaseFirstBlockLength_eq
    {entrance horizon blockLength : ℕ}
    (hremaining : entrance + 2 * blockLength ≤ horizon)
    (hblockLength : 0 < blockLength) :
    tailMergedBlockLength entrance horizon blockLength 0 = blockLength := by
  have htwo : 0 + 1 <
      tailMergedBlockCount entrance horizon blockLength := by
    unfold tailMergedBlockCount
    have htwo' : 2 * blockLength ≤ horizon - entrance := by omega
    have hdiv : 2 ≤ (horizon - entrance) / blockLength := by
      exact (Nat.le_div_iff_mul_le hblockLength).2 (by omega)
    omega
  exact tailMergedBlockLength_interior htwo

/-- The endpoint interval already supplied by the three robust entrance
constructions lies in the first block's central window. -/
lemma staircaseFirstInteriorWindow
    {entrance horizon blockLength : ℕ}
    {base width drift : ℝ}
    (hremaining : entrance + 2 * blockLength ≤ horizon)
    (hblockLength : 0 < blockLength)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hcost : 10 * drift * (blockLength : ℝ) < width ^ 3) :
    Set.Icc
      (base + drift * (entrance : ℝ) / width ^ 2 + 2 * width / 5)
      (base + drift * (entrance : ℝ) / width ^ 2 + 3 * width / 5) ⊆
    Set.Icc
      (staircaseLowerEdge base drift width
        (tailMergedBlockStart entrance horizon blockLength) 0 +
        staircaseTubeWidth width drift
          (tailMergedBlockLength entrance horizon blockLength) 0 / 3)
      (staircaseLowerEdge base drift width
        (tailMergedBlockStart entrance horizon blockLength) 0 +
        2 * staircaseTubeWidth width drift
          (tailMergedBlockLength entrance horizon blockLength) 0 / 3) := by
  have htwo : 0 < tailMergedBlockCount entrance horizon blockLength :=
    tailMergedBlockCount_pos_of_start_add_blockLength_le
      hblockLength (by omega)
  have hfirstLength := staircaseFirstBlockLength_eq hremaining hblockLength
  have hstartZero :
      tailMergedBlockStart entrance horizon blockLength 0 = entrance :=
    tailMergedBlockStart_zero htwo
  have hstartOne : tailMergedBlockStart entrance horizon blockLength 1 =
      entrance + blockLength := by
    have hnext : tailMergedBlockStart entrance horizon blockLength 1 =
        tailMergedBlockStart entrance horizon blockLength 0 +
          tailMergedBlockLength entrance horizon blockLength 0 :=
      tailMergedBlockStart_next_eq_add_length
        (by omega : entrance ≤ horizon) 0
    simpa [hstartZero, hfirstLength] using hnext
  have hsq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hdelta : 10 * (drift * (blockLength : ℝ) / width ^ 2) < width := by
    rw [show 10 * (drift * (blockLength : ℝ) / width ^ 2) =
      10 * drift * (blockLength : ℝ) / width ^ 2 by ring]
    apply (div_lt_iff₀ hsq).2
    nlinarith [hcost]
  have hadd : drift * ((entrance + blockLength : ℕ) : ℝ) / width ^ 2 =
      drift * (entrance : ℝ) / width ^ 2 +
        drift * (blockLength : ℝ) / width ^ 2 := by
    push_cast
    ring
  have hdeltaNonneg :
      0 ≤ drift * (blockLength : ℝ) / width ^ 2 := by positivity
  intro y hy
  rcases hy with ⟨hyl, hyu⟩
  constructor
  · simp only [staircaseLowerEdge, staircaseTubeWidth,
      hstartOne, hfirstLength]
    rw [hadd]
    nlinarith [hdelta, hdeltaNonneg]
  · simp only [staircaseLowerEdge, staircaseTubeWidth,
      hstartOne, hfirstLength]
    rw [hadd]
    nlinarith [hdeltaNonneg]

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

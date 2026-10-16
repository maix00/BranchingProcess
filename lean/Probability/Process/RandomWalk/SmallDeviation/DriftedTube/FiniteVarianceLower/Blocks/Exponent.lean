/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Proof.Staircase.Product
/-!
# Exponential cost of a finite staircase

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.sum_blockLengths_add_start`:
  consecutive block lengths satisfy
  $t_0+\sum_{j<q}|I_j|=t_q$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.prod_exp_blockLengths`:
  $\prod_{j<q}\exp(-d|I_j|/D^2)
  =\exp(-d(t_q-t_0)/D^2)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exp_totalCost_le_mul_entrance_blockCost`:
  the entrance budget with rate $d'-d''$ and the staircase budget with
  rate $d''$ together dominate $\exp(-d'L/D^2)$.

This is the deterministic exponential calculation after the reverse Markov
product in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lengths of consecutive blocks telescope to the difference of their
starting and ending times. -/
theorem sum_blockLengths_add_start
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q : ℕ) :
    start 0 + ∑ j ∈ Finset.range q, length j = start q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, hnext q]
      omega

/-- The finite product of block exponentials is the exponential cost of
the total block time. -/
theorem prod_exp_blockLengths
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q : ℕ) (d width : ℝ) :
    (∏ j ∈ Finset.range q,
      Real.exp (-d * (length j : ℝ) / width ^ 2)) =
      Real.exp (-d * ((start q - start 0 : ℕ) : ℝ) / width ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  have hsum : (∑ j ∈ Finset.range q, length j) =
      start q - start 0 := by
    have h := sum_blockLengths_add_start start length hnext q
    omega
  calc
    (∑ j ∈ Finset.range q,
      -d * (length j : ℝ) / width ^ 2) =
        -d / width ^ 2 *
          (∑ j ∈ Finset.range q, (length j : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -d * ((start q - start 0 : ℕ) : ℝ) / width ^ 2 := by
      rw [← Nat.cast_sum, hsum]
      ring

/-- The entrance and staircase exponential costs fit the total rate
budget because the staircase begins after a nonnegative transition time. -/
theorem exp_totalCost_le_mul_entrance_blockCost
    {transition horizon : ℕ} {width totalRate blockRate : ℝ}
    (htransition : transition ≤ horizon)
    (hblockRate : 0 ≤ blockRate) :
    Real.exp (-totalRate * (horizon : ℝ) / width ^ 2) ≤
      Real.exp (-(totalRate - blockRate) * (horizon : ℝ) / width ^ 2) *
        Real.exp (-blockRate * ((horizon - transition : ℕ) : ℝ) /
          width ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hidentity :
      -(totalRate - blockRate) * (horizon : ℝ) / width ^ 2 +
          -blockRate * ((horizon - transition : ℕ) : ℝ) / width ^ 2 =
        -totalRate * (horizon : ℝ) / width ^ 2 +
          blockRate * (transition : ℝ) / width ^ 2 := by
    rw [Nat.cast_sub htransition]
    ring
  rw [hidentity]
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg hblockRate (Nat.cast_nonneg _))
      (sq_nonneg _))

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Exponential cost of a finite staircase

The supporting lemmas in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.sum_blockLengths_add_start`:
  consecutive block lengths satisfy
  $t_0+\sum_{j<q}|I_j|=t_q$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.prod_exp_blockLengths`:
  $\prod_{j<q}\exp(-d|I_j|/D^2)
  =\exp(-d(t_q-t_0)/D^2)$.

These generic block-schedule identities are used in the finite staircase
calculation in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The lengths of consecutive blocks telescope to the difference of their
starting and ending times. -/
lemma sum_blockLengths_add_start
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
lemma prod_exp_blockLengths
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

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end

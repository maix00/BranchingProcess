/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Exponential costs in a finite staircase

## Internal proof declarations

The two identities are

$$
\prod_{j<q}e^{-d\ell_j/W^2}
=e^{-d(s_q-s_0)/W^2},
\qquad
 e^{-R n/W^2}\leq e^{-(R-r)n/W^2}e^{-r(n-s)/W^2}
\quad(s\leq n,\ r\geq0).
$$

This file groups the two exponential-cost estimates used by the lower- and
upper-endpoint finite-staircase calculations in Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
proof of Lemma 3.5. The block-time telescoping step uses Mathlib's general
`Finset.sum_range_tsub` theorem, and the finite exponential product uses
`Real.exp_sum`.
-/

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

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
    calc
      (∑ j ∈ Finset.range q, length j) =
          ∑ j ∈ Finset.range q, (start (j + 1) - start j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hnext j]
        omega
      _ = start q - start 0 :=
        Finset.sum_range_tsub
          (monotone_nat_of_le_succ fun j => by
            rw [hnext j]
            omega) q
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
lemma exp_totalCost_le_mul_entrance_blockCost
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

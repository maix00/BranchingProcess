/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
/-!
# Entrance and staircase exponential cost

The module-visible supporting lemma in this proof file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exp_totalCost_le_mul_entrance_blockCost`:
  the entrance budget with rate $d'-d''$ and the staircase budget with
  rate $d''$ together dominate $\exp(-d'L/D^2)$.

This rate allocation is used in the finite staircase proof of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

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

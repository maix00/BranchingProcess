/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Gaussian.Interval

/-!
# Finite products of Gaussian interval probabilities

These inequalities concern only the nondegenerate real Gaussian law and a
finite family of intervals.  They are used by small-deviation arguments, but
do not depend on random-walk paths, block lengths, or a Mogulskii scale.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- A finite product of standard Gaussian interval probabilities is positive
when every interval has positive radius and the common scale is positive. -/
theorem prod_gaussian_Ioo_sub_add_pos
    {constant blockRadius : ℝ} (hconstant : 0 < constant)
    (hblockRadius : 0 < blockRadius) {blocks : ℕ}
    (target : Fin blocks → ℝ) :
    0 < ∏ j : Fin blocks,
      gaussianReal 0 1
        (Ioo
          ((target j - blockRadius) / Real.sqrt constant)
          ((target j + blockRadius) / Real.sqrt constant)) := by
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (gaussianReal_Ioo_pos (μ := 0) (v := 1) (by norm_num)
    (div_lt_div_of_pos_right (by linarith)
      (Real.sqrt_pos.2 hconstant))).ne'

/-- Shrinking a positive common scale below one only enlarges the symmetric
Gaussian interval in a finite product. -/
theorem prod_gaussian_Ioo_one_le_of_constant_le_one
    {constant blockRadius : ℝ} (hconstant : 0 < constant)
    (hconstantOne : constant ≤ 1) (hblockRadius : 0 < blockRadius)
    (blocks : ℕ) :
    (∏ _j : Fin blocks,
        gaussianReal 0 1 (Ioo (-blockRadius) blockRadius)) ≤
      ∏ _j : Fin blocks,
        gaussianReal 0 1
          (Ioo
            (-blockRadius / Real.sqrt constant)
            (blockRadius / Real.sqrt constant)) := by
  apply Finset.prod_le_prod
  intro j hj
  apply measure_mono
  intro x hx
  have hsqrtPos : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hsqrtOne : Real.sqrt constant ≤ 1 := Real.sqrt_le_one.2 hconstantOne
  constructor
  · have hright : blockRadius ≤ blockRadius / Real.sqrt constant := by
      exact (le_div_iff₀ hsqrtPos).2
        (mul_le_of_le_one_right hblockRadius.le hsqrtOne)
    have hleft : -blockRadius / Real.sqrt constant ≤ -blockRadius := by
      simpa only [neg_div] using neg_le_neg hright
    exact hleft.trans_lt hx.1
  · have hright : blockRadius ≤ blockRadius / Real.sqrt constant := by
      exact (le_div_iff₀ hsqrtPos).2
        (mul_le_of_le_one_right hblockRadius.le hsqrtOne)
    exact hx.2.trans_le hright

/-- If a center shift is at most half the block radius, every shifted Gaussian
interval in a finite product contains the fixed interval with half that
radius. -/
theorem prod_gaussian_Ioo_halfRadius_le_linearReturn
    {constant blockRadius y : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (hshift : |y / (blocks : ℝ)| ≤ blockRadius / 2) :
    (∏ _j : Fin blocks,
        gaussianReal 0 1
          (Ioo
            (-(blockRadius / 2) / Real.sqrt constant)
            ((blockRadius / 2) / Real.sqrt constant))) ≤
      ∏ _j : Fin blocks,
        gaussianReal 0 1
          (Ioo
            (((-y / (blocks : ℝ)) - blockRadius) /
              Real.sqrt constant)
            (((-y / (blocks : ℝ)) + blockRadius) /
              Real.sqrt constant)) := by
  have hsqrt : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hshift' : |-y / (blocks : ℝ)| ≤ blockRadius / 2 := by
    rw [neg_div, abs_neg]
    exact hshift
  rw [abs_le] at hshift'
  apply Finset.prod_le_prod
  intro j hj
  apply measure_mono
  intro x hx
  constructor
  · apply lt_of_le_of_lt _ hx.1
    apply (div_le_div_iff_of_pos_right hsqrt).2
    linarith [hshift'.1]
  · apply lt_of_lt_of_le hx.2
    apply (div_le_div_iff_of_pos_right hsqrt).2
    linarith [hshift'.2]

end ProbabilityTheory

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Gaussian.Interval

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite products of Gaussian interval probabilities

For $\gamma(I)=\mathbb P(Z\in I)$ with $Z\sim N(0,1)$, the public results
are:

- `ProbabilityTheory.prod_gaussian_Ioo_sub_add_pos`: if $c>0$, $R>0$, and
  $t_0,\ldots,t_{k-1}\in\mathbb R$, then
  $\prod_{j<k}\gamma(((t_j-R)/\sqrt c,(t_j+R)/\sqrt c))>0$.
- `ProbabilityTheory.prod_gaussian_Ioo_one_le_of_constant_le_one`: if
  $0<c\leq1$ and $R>0$, then
  $\prod_{j<k}\gamma((-R,R))\leq
   \prod_{j<k}\gamma((-R/\sqrt c,R/\sqrt c))$.

These facts concern finite products of nondegenerate real Gaussian interval
probabilities; their statements do not depend on random-walk paths or on a
small-deviation scale.
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

end ProbabilityTheory

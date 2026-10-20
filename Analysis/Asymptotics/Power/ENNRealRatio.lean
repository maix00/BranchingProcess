/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Basic.ENNReal.Real

/-!
# Power rates for moment ratios

* `Asymptotics.ennreal_rpow_div_toReal_ge_of_power_bounds`: if
  `N > 0`, `q ≥ 0`, `N ^ α ≤ x.toReal`, and `0 < y < ∞` with
  `y.toReal ≤ N ^ β`, then
  `N ^ (q * α - β) ≤ (x ^ q / y).toReal`.

This statement combines lower and upper power bounds for extended
nonnegative quantities. It is independent of a particular random variable
or branching model.
-/

@[expose] public section

open scoped ENNReal

namespace Asymptotics

/-- Lower and upper power bounds for extended nonnegative quantities give the
corresponding power bound for their moment ratio. -/
theorem ennreal_rpow_div_toReal_ge_of_power_bounds
    {x y : ENNReal} {N α β q : ℝ}
    (hN : 0 < N) (hq : 0 ≤ q)
    (hyTop : y ≠ ∞) (hyPos : 0 < y)
    (hx : N ^ α ≤ x.toReal) (hy : y.toReal ≤ N ^ β) :
    N ^ (q * α - β) ≤ (x ^ q / y).toReal := by
  have hmoment : N ^ (q * α) ≤ x.toReal ^ q := by
    calc
      N ^ (q * α) = N ^ (α * q) := by rw [mul_comm]
      _ = (N ^ α) ^ q := by rw [← Real.rpow_mul hN.le]
      _ ≤ x.toReal ^ q :=
        Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hx hq
  have hyRealPos : 0 < y.toReal := ENNReal.toReal_pos hyPos.ne' hyTop
  have hmul : N ^ (q * α - β) * y.toReal ≤ x.toReal ^ q := by
    calc
      N ^ (q * α - β) * y.toReal ≤ N ^ (q * α - β) * N ^ β :=
        mul_le_mul_of_nonneg_left hy (Real.rpow_nonneg hN.le _)
      _ = N ^ (q * α) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ x.toReal ^ q := hmoment
  have hratio : N ^ (q * α - β) ≤ x.toReal ^ q / y.toReal :=
    (le_div_iff₀ hyRealPos).2 hmul
  simpa only [ENNReal.toReal_div, ENNReal.toReal_rpow] using hratio

end Asymptotics

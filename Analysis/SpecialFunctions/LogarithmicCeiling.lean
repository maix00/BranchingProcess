/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Natural power bounds from real logarithmic ceilings

For positive $x$ and a base $b>1$, the natural ceiling of $\log_b x$ gives
an integer exponent whose power of $b$ reaches $x$.

## Public declarations

- `Real.le_pow_natCeil_logb` states
  $x\le b^{\lceil\log_b x\rceil_+}$ for $x>0$ and $b>1$.

Mathlib provides the real logarithm in base $b$, its inverse identity with
real powers, and monotonicity of real powers in the exponent. This theorem
packages those facts with the natural ceiling used to choose discrete
exponential time horizons.
-/

@[expose] public section

namespace Real

/-- A positive target is reached by the natural ceiling of its logarithm in
any base greater than one. -/
theorem le_pow_natCeil_logb {b x : ℝ} (hb : 1 < b) (hx : 0 < x) :
    x ≤ b ^ ⌈logb b x⌉₊ := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hceil : logb b x ≤ (⌈logb b x⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_ceil (logb b x)
  calc
    x = b ^ logb b x := (rpow_logb hbpos hb.ne' hx).symm
    _ ≤ b ^ (⌈logb b x⌉₊ : ℝ) :=
      rpow_le_rpow_of_exponent_le hb.le hceil
    _ = b ^ ⌈logb b x⌉₊ := by rw [← rpow_natCast]

end Real

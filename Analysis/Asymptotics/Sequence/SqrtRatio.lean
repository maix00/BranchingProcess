/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Square-root ratios of real sequences

## Public declarations

- `Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero`:
  from $a_n\ge0$, eventual positivity of $b_n$, and
  $a_n^2/b_n\to0$, conclude $a_n/\sqrt{b_n}\to0$.

This is a general real-sequence limit and does not depend on a small-deviation
scale.
-/

@[expose] public section

open Filter

namespace Asymptotics

/-- If `f` is nonnegative and `f n ^ 2 / g n → 0` for an eventually positive
normalization `g`, then `f n / √(g n) → 0`. -/
theorem tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hg : ∀ᶠ n in atTop, 0 < g n)
    (hsq : Tendsto (fun n : ℕ => (f n ^ 2) / g n) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => f n / Real.sqrt (g n)) atTop (nhds 0) := by
  have hroot : Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘ (fun n : ℕ => f n ^ 2 / g n))
      atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  have heq : (fun n : ℕ => f n / Real.sqrt (g n)) =ᶠ[atTop]
      ((fun x : ℝ => Real.sqrt x) ∘ (fun n : ℕ => f n ^ 2 / g n)) := by
    filter_upwards [hg] with n hgn
    change f n / Real.sqrt (g n) = Real.sqrt (f n ^ 2 / g n)
    rw [Real.sqrt_div (sq_nonneg (f n)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hf n)]
  exact hroot.congr' heq.symm

end Asymptotics

end

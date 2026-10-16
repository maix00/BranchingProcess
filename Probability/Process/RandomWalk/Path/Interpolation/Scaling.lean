/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Basic

/-!
# Scaling polygonal random-walk paths

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.normalizedLinearPath_div_const_eq`:
  the polygonal path of $(x_j/\sigma)$ normalized by $\sqrt n$ equals
  the path of $(x_j)$ normalized by $\sigma\sqrt n$.
- `ProbabilityTheory.RandomWalk.normalizedLinearContinuousPathIcc_div_const_eq`:
  the same equality as continuous maps on $[0,1]$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Positive variance normalization commutes with polygonal interpolation. -/
theorem normalizedLinearPath_div_const_eq
    {n : ℕ} (hn : 0 < n) {sigma : ℝ} (hsigma : 0 < sigma)
    (increment : ℕ → ℝ) (t : ℝ) :
    normalizedLinearPath (fun _ => Real.sqrt n) n
        (fun j => increment j / sigma) t =
      normalizedLinearPath (fun _ => sigma * Real.sqrt n) n increment t := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [normalizedLinearPath]
  have hsum :
      (∑ k ∈ Finset.range n,
        linearIncrementWeight n k t * (increment k / sigma)) =
      (∑ k ∈ Finset.range n,
        linearIncrementWeight n k t * increment k) / sigma := by
    simp [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rw [hsum]
  field_simp [hsigma.ne', hsqrt.ne']

/-- The path-valued form of positive variance normalization. -/
theorem normalizedLinearContinuousPathIcc_div_const_eq
    {n : ℕ} (hn : 0 < n) {sigma : ℝ} (hsigma : 0 < sigma)
    (increment : ℕ → ℝ) :
    normalizedLinearContinuousPathIcc (fun _ => Real.sqrt n) n
        (fun j => increment j / sigma) =
      normalizedLinearContinuousPathIcc
        (fun _ => sigma * Real.sqrt n) n increment := by
  ext t
  exact normalizedLinearPath_div_const_eq hn hsigma increment t

end ProbabilityTheory.RandomWalk

end

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Probability.Distributions.Stable.Attraction.Norming.Basic

/-!
# Stable norming at index two

The public theorem in this file is:

- `ProbabilityTheory.IsStableNorming.tendsto_div_sqrt_nat`:
  if $b_n$ is an index-two stable norming for a law with finite second moment,
  then $b_n/\sqrt n$ converges to the square root of that second moment.

This is the deterministic normalization step used to pass from the stable
index-two route to the finite-variance form of Donsker's theorem.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The same statement in the normalization used by Donsker's theorem. -/
theorem IsStableNorming.tendsto_div_sqrt_nat
    {ν : Measure ℝ} (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℕ → ℝ} (h : IsStableNorming 2 ν b) :
    Tendsto (fun n : ℕ => b n / Real.sqrt n) atTop
      (nhds (Real.sqrt (∫ x : ℝ, x ^ 2 ∂ν))) := by
  have hsq := h.tendsto_sq_div_nat hν
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (b n ^ 2 / (n : ℝ))) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂ν))) :=
    (Real.continuous_sqrt.tendsto _).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbn : 0 < b n := h.1 n hn
  have hrewrite : b n ^ 2 / (n : ℝ) = (b n / Real.sqrt n) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hrewrite, Real.sqrt_sq
    (div_nonneg hbn.le (Real.sqrt_nonneg n))]

end ProbabilityTheory

end

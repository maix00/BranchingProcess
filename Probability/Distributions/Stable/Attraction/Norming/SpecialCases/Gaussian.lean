/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Distributions.Moments.Truncated.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Basic

/-!
# The stable truncated second moment for Gaussian laws

The public theorem in this file is:

- `ProbabilityTheory.tendsto_stableSlowVariation_two_gaussianReal_zero`:
  for a centered Gaussian law with variance $v$, the exponent-two stable
  truncated-moment factor $L^*(u)$ converges to $v$ as $u\to\infty$.

This identifies the Gaussian specialization of the general truncated-second-
moment limit in `Probability.Distributions.Moments.Truncated`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory

/-- For a centered Gaussian stable law, Mogulskii's `L*` at exponent two
converges to the variance parameter. -/
theorem tendsto_stableSlowVariation_two_gaussianReal_zero (v : ℝ≥0) :
    Tendsto (stableSlowVariation 2 (gaussianReal 0 v)) Filter.atTop
      (nhds (v : ℝ)) := by
  have hintegrable : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    simpa [id] using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hsecond : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
    have hvariance : variance id (gaussianReal 0 v) = (v : ℝ) :=
      variance_id_gaussianReal
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable (by simp)] at hvariance
    simpa [id] using hvariance
  have h := tendsto_truncatedSecondMoment (gaussianReal 0 v) hintegrable
  rw [hsecond] at h
  convert h using 1
  funext u
  exact stableSlowVariation_two _ _

end ProbabilityTheory

end

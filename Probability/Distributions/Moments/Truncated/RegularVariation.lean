/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

module

public import Analysis.Asymptotics.RegularVariation
public import Probability.Distributions.Moments.Truncated

/-!
# Regular variation of truncated second moments

This file records the fixed-scale consequence of slow variation for the
two-sided tail relative to a truncated second moment.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- If the truncated second moment is slowly varying and the two-sided tail
is negligible after multiplication by `x²`, then it is still negligible at
any fixed positive rescaling of the cutoff, relative to the original
truncated second moment. -/
theorem tendsto_rescaledSecondTailRatio_of_slowVariation
    (μ : Measure ℝ)
    (hVslow : Asymptotics.IsSlowlyVaryingAtTop (truncatedSecondMoment μ))
    (hTail : Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | x < |y|} /
        truncatedSecondMoment μ x) atTop (nhds 0))
    (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun x : ℝ => x ^ 2 * μ.real {y : ℝ | c * x < |y|} /
        truncatedSecondMoment μ x)
      atTop (nhds 0) := by
  let V : ℝ → ℝ := truncatedSecondMoment μ
  let tail : ℝ → ℝ := fun x => μ.real {y : ℝ | x < |y|}
  have hVscale : Tendsto (fun x : ℝ => V (c * x) / V x) atTop (nhds 1) := by
    simpa [V, Real.rpow_zero] using hVslow.ratio_tendsto hc
  have htailScale : Tendsto
      (fun x : ℝ => (c * x) ^ 2 * tail (c * x) / V (c * x))
      atTop (nhds 0) := by
    have hscale : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    exact hTail.comp hscale
  have hprod := htailScale.mul hVscale
  have hconst := hprod.const_mul (c⁻¹ ^ 2)
  have hVcx : ∀ᶠ x : ℝ in atTop, 0 < V (c * x) := by
    exact (tendsto_id.const_mul_atTop hc).eventually hVslow.eventually_pos
  have heq : (fun x : ℝ => c⁻¹ ^ 2 *
      ((c * x) ^ 2 * tail (c * x) / V (c * x) *
        (V (c * x) / V x))) =ᶠ[atTop]
      fun x => x ^ 2 * tail (c * x) / V x := by
    filter_upwards [hVcx] with x hx
    field_simp [ne_of_gt hc, ne_of_gt hx]
  have hconst' : Tendsto
      (fun x : ℝ => c⁻¹ ^ 2 *
        ((c * x) ^ 2 * tail (c * x) / V (c * x) *
          (V (c * x) / V x))) atTop (nhds 0) := by
    simpa using hconst
  have hresult := hconst'.congr' heq
  simpa [V, tail] using hresult

end ProbabilityTheory

end

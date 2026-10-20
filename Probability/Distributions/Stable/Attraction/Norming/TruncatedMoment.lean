/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Basic
public import Probability.Distributions.Moments.Truncated.Basic

/-!
# Truncated-moment limits for the stable norming factor

The public theorems are:

- `ProbabilityTheory.tendsto_stableSlowVariation_of_layercake_and_tail`:
  if $u^{\alpha-2}$ times the layer-cake tail integral tends to $A$ and
  $u^\alpha\nu(|x|>u)\to B$, then the stable norming factor $L^*(u)$ tends to
  $A-B$.
- `ProbabilityTheory.tendsto_stableSlowVariation_of_twoSidedTail`:
  if $0<\alpha<2$ and $u^\alpha\nu(|x|>u)\to B>0$, then
  $L^*(u)\to\alpha B/(2-\alpha)$.

Here $L^*(u)=u^{\alpha-2}\int_{|x|\le u}x^2\,\nu(dx)$. These are
distributional consequences of the general truncated-moment identities in
`Probability.Distributions.Moments.Truncated`; they require no path-space or
small-deviation assumptions.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A finite layer-cake limit and two-sided tail limit determine the
stable-domain factor `L*` from the truncated moment. -/
theorem tendsto_stableSlowVariation_of_layercake_and_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral ν u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop (nhds (A - B)) := by
  change Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment ν u)
    atTop (nhds (A - B))
  exact tendsto_truncatedSecondMoment_scale_of_layercake_and_tail ν hA hB

/-- A two-sided power-tail asymptotic determines the stable-domain factor
`L*` from the truncated moment. If `u^α μ(|x| > u) → B` with `0 < α < 2`,
then `u^(α-2) ∫_{|x|≤u} x² ν(dx) → α B / (2-α)`. -/
theorem tendsto_stableSlowVariation_of_twoSidedTail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {α B : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop
      (nhds (α * B / (2 - α))) := by
  change Tendsto (fun u => u ^ (α - 2) * truncatedSecondMoment ν u) atTop _
  exact tendsto_truncatedSecondMoment_scale_of_twoSidedTail ν hα₀ hα₂ hB hTail

end ProbabilityTheory

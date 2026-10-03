module

public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Distributions.Moments.Truncated

/-!
# Stable-domain specialization of the truncated-moment tail theorem

The measure argument is the input increment law.  The generic layer-cake and
power-tail results are in `Probability.Distributions.Moments.Truncated`.
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

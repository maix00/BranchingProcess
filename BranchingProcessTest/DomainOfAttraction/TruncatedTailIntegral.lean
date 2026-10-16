import Probability.Distributions.Moments.Truncated.TailIntegral

open MeasureTheory ProbabilityTheory
open scoped Topology

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hTail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => μ.real {x : ℝ | u < |x|}) (-α)) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t)
      (3 - α) :=
  (ProbabilityTheory.IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail
    μ hα₀ hα₂).mp hTail

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hIntegral : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t)
      (3 - α)) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => μ.real {x : ℝ | u < |x|}) (-α) :=
  (ProbabilityTheory.IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail
    μ hα₀ hα₂).mpr hIntegral

example (μ : Measure ℝ) [IsProbabilityMeasure μ] {α : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hIntegral : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ∫ t in (0:ℝ)..u, truncatedSquareTailIntegral μ t)
      (3 - α)) :
    Asymptotics.IsSlowlyVaryingAtTop
      (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment μ u) :=
  truncatedSecondMomentFactor_isSlowlyVarying_of_integratedTruncatedSquareTail
    μ hα₀ hα₂ hIntegral

#print axioms ProbabilityTheory.firstTailIntegral_twoSidedTail_eq_half_truncatedSquareTailIntegral
#print axioms ProbabilityTheory.secondTailIntegral_twoSidedTail_eq_half_intervalIntegral_truncatedSquareTailIntegral
#print axioms ProbabilityTheory.IsRegularlyVaryingAtTop.twoSidedTail_iff_integratedTruncatedSquareTail
#print axioms ProbabilityTheory.truncatedSecondMomentFactor_isSlowlyVarying_of_integratedTruncatedSquareTail

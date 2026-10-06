import Probability.Distributions.Stable.Attraction.Normal

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Distributional attraction alone gives the Gaussian characteristic-defect
data, with no moment assumption. -/
example {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν (gaussianReal 0 1) scale center) :
    Asymptotics.IsRegularlyVaryingAtZero
        (fun u : ℝ => 1 - ‖charFun ν u‖ ^ 2) 2 ∧
      Tendsto scale atTop atTop ∧
      Tendsto (fun n : ℕ => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹)‖ ^ 2)) atTop (nhds 1) :=
  h.gaussian_defect_data

/-- The finite-variance route remains a separate construction with its
canonical normalization. -/
example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hpositive : 0 < ∫ x : ℝ, x ^ 2 ∂ν) :
    IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt ((n : ℝ) * ∫ x : ℝ, x ^ 2 ∂ν)) (fun _ => 0) :=
  isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
    ν hcentered hsquare hpositive

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hpositive : 0 < ∫ x : ℝ, x ^ 2 ∂ν) :
    IsStableNorming 2 ν
      (fun n => Real.sqrt ((n : ℝ) * ∫ x : ℝ, x ^ 2 ∂ν)) :=
  isStableNorming_two_of_integrable_sq ν hsquare hpositive

#print axioms ProbabilityTheory.IsInDomainOfAttractionAlong.gaussian_defect_data
#print axioms ProbabilityTheory.isStableNorming_two_of_integrable_sq

import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.CLT
import Probability.Distributions.Stable.Attraction
import Probability.Distributions.Stable.Gaussian

/-!
# Gaussian stable-domain adapters

The central limit theorem itself belongs to the Donsker layer.  These results
only package its endpoint limit as the explicit Gaussian and then as a
strictly `2`-stable domain-of-attraction witness for the stable Mogulskii
route.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- A centered unit-second-moment increment law has the explicit Gaussian
normalization used by the stable domain-of-attraction interface. -/
theorem isInDomainOfAttractionAlong_gaussianReal_zero_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      (fun n => Real.sqrt n) (fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  · have hnormalized :
        normalizedIidSum (fun n : ℕ => Real.sqrt n) (fun _ => 0) =
          fun (n : ℕ) increment => (Real.sqrt n)⁻¹ * partialSum n increment := by
      funext n increment
      simp [normalizedIidSum, partialSum]
    rw [hnormalized]
    simpa [independentIncrementLaw] using
      tendstoInDistribution_normalizedPartialSum ν hcentered hsecondMoment

/-- The existential domain-of-attraction consequence of the explicit
Gaussian normalization. -/
theorem isInDomainOfAttraction_gaussianReal_zero_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    IsInDomainOfAttraction ν (gaussianReal 0 1) :=
  (isInDomainOfAttractionAlong_gaussianReal_zero_one
    ν hcentered hsecondMoment).isInDomainOfAttraction

/-- The same finite-variance hypothesis gives attraction to a nondegenerate
strictly `2`-stable law. -/
theorem isInAlphaStableDomainOfAttraction_two
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    IsInAlphaStableDomainOfAttraction 2 ν (gaussianReal 0 1) :=
  ⟨(isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable,
    isInDomainOfAttraction_gaussianReal_zero_one ν hcentered hsecondMoment⟩

end ProbabilityTheory.RandomWalk

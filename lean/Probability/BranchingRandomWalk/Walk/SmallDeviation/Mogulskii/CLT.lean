import Probability.BranchingRandomWalk.Walk.Law
import Probability.Distributions.Stable.Attraction
import Probability.Distributions.Stable.Gaussian
import Mathlib.Probability.CentralLimitTheorem

/-!
# Central limit input for Mogulskii estimates

The canonical increment law is a countable product measure.  This file
connects its coordinate maps to mathlib's central limit theorem.  The result
is independent of any corridor or branching construction.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- Every coordinate of the canonical independent-increment law has the
prescribed one-step law. -/
theorem hasLaw_coordinate_independentIncrementLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    HasLaw (fun increment : ℕ → ℝ => increment n) ν
      (independentIncrementLaw ν) where
  aemeasurable := (measurable_pi_apply n).aemeasurable
  map_eq := independentIncrementLaw_coordinate ν n

/-- Coordinate projections under the canonical increment law are identically
distributed. -/
theorem identDistrib_coordinate_independentIncrementLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (i j : ℕ) :
    IdentDistrib (fun increment : ℕ → ℝ => increment i)
      (fun increment => increment j)
      (independentIncrementLaw ν) (independentIncrementLaw ν) :=
  (hasLaw_coordinate_independentIncrementLaw ν i).identDistrib
    (hasLaw_coordinate_independentIncrementLaw ν j)

/-- The canonical i.i.d. random walk with centered, unit-second-moment
increments satisfies the central limit theorem.  The limiting random
variable is the identity map on its own standard Gaussian probability space.
-/
theorem tendstoInDistribution_normalizedPartialSum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    TendstoInDistribution
      (fun (n : ℕ) increment => (Real.sqrt n)⁻¹ * partialSum n increment)
      atTop id (fun _ => independentIncrementLaw ν) (gaussianReal 0 1) := by
  let X : ℕ → (ℕ → ℝ) → ℝ := fun n increment => increment n
  have hX (n : ℕ) : HasLaw (X n) ν (independentIncrementLaw ν) :=
    hasLaw_coordinate_independentIncrementLaw ν n
  have hzero : (independentIncrementLaw ν)[X 0] = 0 := by
    rw [(hX 0).integral_eq, hcentered]
  have hone : (independentIncrementLaw ν)[(X 0) ^ 2] = 1 := by
    rw [show (X 0) ^ 2 = (fun x : ℝ => x ^ 2) ∘ X 0 by rfl,
      (hX 0).integral_comp (continuous_pow 2).aestronglyMeasurable,
      hsecondMoment]
  have hident : ∀ i : ℕ,
      IdentDistrib (X i) (X 0)
        (independentIncrementLaw ν) (independentIncrementLaw ν) :=
    fun i => identDistrib_coordinate_independentIncrementLaw ν i 0
  simpa [X, partialSum] using
    (tendstoInDistribution_inv_sqrt_mul_sum
      (P := independentIncrementLaw ν)
      (P' := gaussianReal 0 1)
      (X := X) (Y := id)
      (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))
      hzero hone (independentIncrementLaw_independent ν) hident)

/-- The centered unit-second-moment hypothesis places the increment law in
the domain of attraction of the standard Gaussian law. -/
theorem isInDomainOfAttraction_gaussianReal_zero_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    IsInDomainOfAttraction ν (gaussianReal 0 1) := by
  refine ⟨(fun n => Real.sqrt n), (fun _ => 0), ?_, ?_⟩
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

/-- The same finite-variance hypothesis gives attraction to a nondegenerate
strictly `2`-stable law. -/
theorem isInAlphaStableDomainOfAttraction_two
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    IsInAlphaStableDomainOfAttraction 2 ν (gaussianReal 0 1) :=
  ⟨(isStrictlyAlphaStable_gaussianReal_zero (by norm_num)).isAlphaStable,
    isInDomainOfAttraction_gaussianReal_zero_one ν hcentered hsecondMoment⟩

end ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Law
public import Probability.ConvergenceInDistribution.Portmanteau
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Central limit input for the Donsker theorem

The canonical increment law is a countable product measure.  This file
connects its coordinate maps to mathlib's central limit theorem.  The result
is independent of any corridor or branching construction.
-/

open Filter MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

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

/-- The Portmanteau lower bound for an open interval, specialized to the
canonical centered finite-variance random walk. -/
theorem gaussianReal_Ioo_le_liminf_normalizedPartialSum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : ℝ) :
    gaussianReal 0 1 (Set.Ioo lower upper) ≤
      atTop.liminf (fun n : ℕ =>
        (independentIncrementLaw ν).map
          (fun increment => (Real.sqrt n)⁻¹ * partialSum n increment)
          (Set.Ioo lower upper)) := by
  have h := (tendstoInDistribution_normalizedPartialSum ν
    hcentered hsecondMoment).measure_map_le_liminf_of_isOpen
      (isOpen_Ioo : IsOpen (Set.Ioo lower upper))
  simpa using h

/-- The corresponding Portmanteau upper bound for a closed interval. -/
theorem limsup_normalizedPartialSum_le_gaussianReal_Icc
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : ℝ) :
    atTop.limsup (fun n : ℕ =>
        (independentIncrementLaw ν).map
          (fun increment => (Real.sqrt n)⁻¹ * partialSum n increment)
          (Set.Icc lower upper)) ≤
      gaussianReal 0 1 (Set.Icc lower upper) := by
  have h := (tendstoInDistribution_normalizedPartialSum ν
    hcentered hsecondMoment).limsup_measure_map_le_of_isClosed
      (isClosed_Icc : IsClosed (Set.Icc lower upper))
  simpa using h

end ProbabilityTheory.RandomWalk

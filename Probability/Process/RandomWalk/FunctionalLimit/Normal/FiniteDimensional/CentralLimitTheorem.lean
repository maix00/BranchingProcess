/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.Basic
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.ConvergenceInDistribution.Portmanteau
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Central limit theorem for canonical i.i.d. random walks

The canonical increment law is a countable product measure. This file
identifies its coordinate maps with Mathlib's central limit theorem and gives
the corresponding open- and closed-interval probability bounds. These results
are independent of a path-space functional limit or corridor construction.

## Public declarations

- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedPartialSum`:
  for centered, unit-second-moment increments with law $\nu$,
  $S_n/\sqrt n\Rightarrow N(0,1)$ under `iidSequenceLaw ν`.
- `ProbabilityTheory.RandomWalk.gaussianReal_Ioo_le_liminf_normalizedPartialSum`:
  for every open interval $(a,b)$, its standard Gaussian mass is at most the
  liminf of the probabilities that $S_n/\sqrt n\in(a,b)$.
- `ProbabilityTheory.RandomWalk.limsup_normalizedPartialSum_le_gaussianReal_Icc`:
  for every closed interval $[a,b]$, the limsup of the probabilities that
  $S_n/\sqrt n\in[a,b]$ is at most its standard Gaussian mass.

The central limit theorem is Mathlib's
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` from
`Mathlib.Probability.CentralLimitTheorem`; this module identifies the
coordinates of `iidSequenceLaw ν` with that theorem's independent,
identically distributed sequence.
-/

open Filter MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Every coordinate of the canonical independent-increment law has the
prescribed one-step law. -/
private lemma hasLaw_coordinate_iidSequenceLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (n : ℕ) :
    HasLaw (fun increment : ℕ → ℝ => increment n) ν
      (iidSequenceLaw ν) where
  aemeasurable := (measurable_pi_apply n).aemeasurable
  map_eq := iidSequenceLaw_map_apply ν n

/-- Coordinate projections under the canonical increment law are identically
distributed. -/
private lemma identDistrib_coordinate_iidSequenceLaw (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (i j : ℕ) :
    IdentDistrib (fun increment : ℕ → ℝ => increment i)
      (fun increment => increment j)
      (iidSequenceLaw ν) (iidSequenceLaw ν) :=
  (hasLaw_coordinate_iidSequenceLaw ν i).identDistrib
    (hasLaw_coordinate_iidSequenceLaw ν j)

/-- The canonical i.i.d. random walk with centered, unit-second-moment
increments satisfies the central limit theorem.  The limiting random
variable is the identity map on its own standard Gaussian probability space.
-/
theorem tendstoInDistribution_normalizedPartialSum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1) :
    TendstoInDistribution
      (fun (n : ℕ) increment => (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment)
      atTop id (fun _ => iidSequenceLaw ν) (gaussianReal 0 1) := by
  let X : ℕ → (ℕ → ℝ) → ℝ := fun n increment => increment n
  have hX (n : ℕ) : HasLaw (X n) ν (iidSequenceLaw ν) :=
    hasLaw_coordinate_iidSequenceLaw ν n
  have hzero : (iidSequenceLaw ν)[X 0] = 0 := by
    rw [(hX 0).integral_eq, hcentered]
  have hone : (iidSequenceLaw ν)[(X 0) ^ 2] = 1 := by
    rw [show (X 0) ^ 2 = (fun x : ℝ => x ^ 2) ∘ X 0 by rfl,
      (hX 0).integral_comp (continuous_pow 2).aestronglyMeasurable,
      hsecondMoment]
  have hident : ∀ i : ℕ,
      IdentDistrib (X i) (X 0)
        (iidSequenceLaw ν) (iidSequenceLaw ν) :=
    fun i => identDistrib_coordinate_iidSequenceLaw ν i 0
  simpa [X, AdditivePath.displacement] using
    (tendstoInDistribution_inv_sqrt_mul_sum
      (P := iidSequenceLaw ν)
      (P' := gaussianReal 0 1)
      (X := X) (Y := id)
      (HasLaw.id : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1))
      hzero hone (iidSequenceLaw_independent ν) hident)

/-- The Portmanteau lower bound for an open interval, specialized to the
canonical centered finite-variance random walk. -/
theorem gaussianReal_Ioo_le_liminf_normalizedPartialSum
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    (lower upper : ℝ) :
    gaussianReal 0 1 (Set.Ioo lower upper) ≤
      atTop.liminf (fun n : ℕ =>
        (iidSequenceLaw ν).map
          (fun increment => (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment)
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
        (iidSequenceLaw ν).map
          (fun increment => (Real.sqrt n)⁻¹ * AdditivePath.displacement n increment)
          (Set.Icc lower upper)) ≤
      gaussianReal 0 1 (Set.Icc lower upper) := by
  have h := (tendstoInDistribution_normalizedPartialSum ν
    hcentered hsecondMoment).limsup_measure_map_le_of_isClosed
      (isClosed_Icc : IsClosed (Set.Icc lower upper))
  simpa using h

end ProbabilityTheory.RandomWalk

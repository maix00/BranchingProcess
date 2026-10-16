/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Continuous
public import Probability.Process.RandomWalk.Path.Interpolation.Convergence
public import Probability.Process.Path.UnitInterval
public import Topology.Cadlag.Skorokhod.Maps.Continuous

/-!
# Skorokhod-space Donsker theorem

The continuous-path Donsker theorem and the vanishing maximal jump transfer
the limit to the canonical right-continuous step realization in Skorokhod
`J₁` space.

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedStepCadlagPath_brownian`:
  a centered unit-variance i.i.d. random walk, scaled by $1/\sqrt n$, has its
  canonical step path converge in Skorokhod $J_1$ to standard Brownian motion.

This is the step-path form of Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Donsker's invariance principle for the normalized right-continuous step
path in Skorokhod `J₁` space. The functional limit is Theorem 4.20 in I.
Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd
ed., Graduate Texts in Mathematics 113, Springer (1991), DOI
10.1007/978-1-4612-0949-2. -/
theorem tendstoInDistribution_normalizedStepCadlagPath_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun n => normalizedStepCadlagPathIcc
        (fun n => Real.sqrt n) n)
      atTop
      (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
      (fun _ => iidSequenceLaw nu) P := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) nu :=
    .of_integral_ne_zero (by rw [hsecondMoment]; norm_num)
  exact tendstoInDistribution_normalizedStepPath_of_continuousLinear
    P nu hsq _
      (tendstoInDistribution_normalizedLinearContinuousPath_brownian
        nu hcentered hsecondMoment hB hcontinuous hmeasurable)

end ProbabilityTheory.RandomWalk

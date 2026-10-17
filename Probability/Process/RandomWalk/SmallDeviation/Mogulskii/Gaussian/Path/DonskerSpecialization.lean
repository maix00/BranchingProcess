/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Donsker input for the Gaussian Mogulskii path theorem

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path.isNormalizedStepFunctionalLimit_two`:
  for centered increments with unit second moment, Donsker's invariance
  principle gives the stable route's normalized-step functional limit, with
  normalization $b_n=\sqrt n$ and the Brownian path law on $[0,1]$.

The theorem is the exponent-two functional-limit specialization used by
Mogulskii, Theorem 3, Section 4, p. 764 of the 1974 Russian original, “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. The Donsker
invariance theorem used here is Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

/-- At `α = 2`, the functional-limit input of the stable route is Donsker's
invariance principle for the normalized right-continuous step path. The
underlying functional limit is Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2. -/
theorem isNormalizedStepFunctionalLimit_two
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0) (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω)) (hmeasurable : ∀ t, Measurable (B t)) :
    IsNormalizedStepFunctionalLimit nu (fun n => Real.sqrt n) P
      (Skorokhod.ofContinuousMap ∘ continuousunitIntervalPath B hcontinuous) :=
  tendstoInDistribution_normalizedStepCadlagPath_brownian
    nu hcentered hsecondMoment hB hcontinuous hmeasurable

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Path

end

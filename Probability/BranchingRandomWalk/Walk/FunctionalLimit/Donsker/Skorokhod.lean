module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Continuous
public import Probability.BranchingRandomWalk.Walk.Path.Interpolation.Convergence
public import Probability.Process.Path.UnitInterval
public import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Skorokhod-space Donsker theorem

The continuous-path Donsker theorem and the vanishing maximal jump transfer
the limit to the canonical right-continuous step realization in Skorokhod
`J₁` space.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- Donsker's invariance principle for the normalized right-continuous step
path in Skorokhod `J₁` space. -/
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
      (fun _ => independentIncrementLaw nu) P := by
  have hsq : Integrable (fun x : ℝ => x ^ 2) nu :=
    .of_integral_ne_zero (by rw [hsecondMoment]; norm_num)
  exact tendstoInDistribution_normalizedStepPath_of_continuousLinear
    P nu hsq _
      (tendstoInDistribution_normalizedLinearContinuousPath_brownian
        nu hcentered hsecondMoment hB hcontinuous hmeasurable)

end ProbabilityTheory.RandomWalk

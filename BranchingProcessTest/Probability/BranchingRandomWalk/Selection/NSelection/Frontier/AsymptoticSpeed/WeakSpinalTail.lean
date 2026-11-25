import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Speed
import Probability.BranchingRandomWalk.Step.Ordering.Spine

open MeasureTheory ProbabilityTheory Filter Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
open scoped Topology

-- Public contract regression: the speed formula accepts the original weak
-- reproductive tail and leftmost first moment. No finite cross weight or
-- logarithmic square moment is supplied, including after offspring ordering.
example (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hnonempty : L.raw nonemptySupport = 1)
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw)
    (hfirst : HasLeftmostFirstMoment L)
    {σ : ℝ} (hσ : 0 < σ)
    (hspine : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) L.sortedPotentialImage) (σ ^ 2)) :
    ∃ speed : ℕ → ℝ,
      Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ 2 * speed N) atTop
        (𝓝 ((Real.pi ^ 2 / 2) * σ ^ 2)) := by
  obtain ⟨speed, _, hlimit⟩ := exists_speed_with_logSq_limit L
    hsuper hnonempty hboundary htail hfirst hσ hspine
  exact ⟨speed, hlimit⟩

#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedFamilyChildLaw_otherWeight
#print axioms ProbabilityTheory.BranchingRandomWalk.HasFiniteCrossWeight.hasSpinalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.StepLaw.tiltedMarkedPotentialLaw_totalWeight_sortedPotentialImage
#print axioms ProbabilityTheory.BranchingRandomWalk.StepLaw.tiltedPotentialLaw_sortedPotentialImage
#print axioms ProbabilityTheory.BranchingRandomWalk.StepLaw.sortedPotentialImage_hasSpinalWeightTail_iff
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_spinalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_initialExponent
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.eventually_logSq_mul_speed_lt_of_firstMoment
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.exists_speed_with_logSq_limit

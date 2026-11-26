import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.FirstMoment
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.L2Limit
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Speed

open MeasureTheory ProbabilityTheory Filter Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open scoped Topology ENNReal

-- Full-capacity contract: the polynomial bound takes no leftmost-child
-- moment, supercriticality, finite cross weight or logarithmic square moment.
example (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization realPotential μ)
    (hne : μ nonemptySupport = 1) (htail : HasSpinalWeightTail realPotential μ)
    {σ t ζ : ℝ} (hσ : 0 < σ)
    (hc : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (σ ^ 2))
    (ht : 0 < t) (hgap : -1 + (Real.pi ^ 2 / 2) * σ ^ 2 * t < ζ)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let I n := RootIndexed.addressLinearOrder (Fin (N n)) ℕ
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      (RootIndexed.stepFieldLaw (Root := ℕ) μ) {field | ζ * Real.log (N n : ℝ) ≤
        @countableRootEndpointMinimum (N n) (N n) (H n) (I n) field} ≤
        ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) :=
  eventually_countableRootEndpointMinimum_ge_le_polynomial_of_fullCapacity
    hN μ hb hne htail hσ hc ht hH hgap

-- Boundary exponent a=1 is included in the first-moment theorem; only
-- the positive first moment of the ordered leftmost child is supplied.
example (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hne : L.raw nonemptySupport = 1)
    (hb : HasBoundaryNormalization L.potential L.raw)
    (htail : HasSpinalWeightTail L.potential L.raw) (hfirst : HasLeftmostFirstMoment L)
    {σ t : ℝ} (hσ : 0 < σ)
    (hc : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1)
      L.sortedPotentialImage) (σ ^ 2)) (ht : 0 < t)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t)) :
    let P := RootIndexed.stepFieldLaw (Root := ℕ) L.sortedPotentialImage
    let m n := ⌊(N n : ℝ) ^ (1 : ℝ)⌋₊
    Tendsto (fun n => eLpNorm (fun field =>
      @countableRootEndpointMinimum (m n) (N n) (H n)
        (RootIndexed.addressLinearOrder (Fin (m n)) ℕ) field / Real.log (N n : ℝ) -
        (-1 + (Real.pi ^ 2 / 2) * σ ^ 2 * t)) 1 P) atTop (𝓝 0) :=
  tendsto_eLpNorm_one_countableRootEndpointMinimum_div_sub_of_spinalWeightTail
    L hne hb htail hfirst hσ hc (a := 1) zero_lt_one le_rfl ht hN hH

#print axioms ProbabilityTheory.tendsto_eLpNorm_one_div_sub_of_lower_tails_and_upper_mean
#print axioms MeasureTheory.tendsto_setIntegral_div_of_polynomial_second_moment_and_exponential_probability
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_fullCapacity
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_eLpNorm_one_countableRootEndpointMinimum_div_sub_of_spinalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_integral_countableRootEndpointMinimum_div_of_spinalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendsto_eLpNorm_two_countableRootEndpointMinimum_div_sub_of_fullCapacity
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.exists_speed_with_logSq_limit

#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_ge_le_polynomial_of_positiveExponent
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_countableRootEndpointMinimum_abs_div_sub_le_polynomial_of_spinalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.tendstoInMeasure_countableRootEndpointMinimum_div_of_spinalWeightTail

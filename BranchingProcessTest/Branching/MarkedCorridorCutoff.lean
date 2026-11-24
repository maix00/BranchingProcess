import Probability.Process.RandomWalk.SmallDeviation.Marked.FiniteVarianceLower
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FamilySelection
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FiniteVariance

open MeasureTheory ProbabilityTheory Combinatorics.Branching Filter
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open scoped ENNReal Topology Classical

-- The long-horizon theorem consumes a joint law, not the product of its
-- marginals. No within-step independence or reproductive log-moment is used.
example (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {σ c α d : ℝ} (hν : IsCenteredSecondMoment (ν.map Prod.fst) (σ ^ 2))
    (hσ : 0 < σ) (hB : HasVanishingQuadraticTail ν Prod.snd)
    (hc : 0 ≤ c) (hα : 0 < α) (hd : (Real.pi ^ 2 / 2) * σ ^ 2 < d)
    {L : ℕ → ℝ} {H : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hH : ∀ᶠ n in atTop, 0 < H n)
    (hscale : Tendsto (fun n => L n ^ 2 / (H n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-d * H n / L n ^ 2)) ≤
      iidSequenceLaw ν (corridorEvent (-(L n / 2)) (L n / 2)
        (c / L n ^ 2) (α * L n) (H n) 0) :=
  eventually_affineCorridorProbability_ge_exp_of_finiteVariance
    ν hν hσ hB hc hα hd hL hH hscale

-- The first child is counted even when its own family is rejected: the
-- endpoint does not reproduce yet. At generation two that rejected family
-- is a strict ancestor, and both of its children are removed. A root-only
-- cutoff would incorrectly retain them.
example :
    let field : StepField ℕ ℝ := fun u i =>
      if u = [] then (if i = 0 then some 0 else none)
      else if i ≤ 1 then some 0 else none
    let A : Set (Step ℕ ℝ) := {ξ | ξ 1 = none}
    surviveAlong field [] [0, 0] ∧
      surviveAlong (fun u => Step.selectFamily A (field u)) [] [0] ∧
      ¬surviveAlong (fun u => Step.selectFamily A (field u)) [] [0, 0] := by
  simp [surviveAlong, Step.selectFamily, survive]

-- Even rejecting every family retains the empty path at generation zero.
example (field : StepField ℕ ℝ) :
    pathGeneration realPotential 0 (fun _ => 1) 0
      (fun u => Step.selectFamily ∅ (field u)) = 1 := by
  simp

-- The selected-law second moment only assumes centering and normalization
-- of the *original* law. There is no finite-cross-weight assumption.
example {X : Type*} [MeasurableSpace X] (φ : Potential X)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization φ μ) {variance v c d : ℝ}
    (hν : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvar : 0 < variance) (hv : 0 < v) (hc : 0 ≤ c)
    (hd : 0 < d) (hcrit : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ D ≥ D₀, ∀ K : ℝ≥0∞, ∀ lower : ℝ,
      -D ≤ lower → lower ≤ 0 → ∀ N : ℕ, 1 ≤ N → ∀ U : ℝ,
      (∫⁻ field, (pathGeneration φ N
        ((ProbabilityTheory.RandomWalk.affineCorridorThrough N lower (c / D ^ 2) D U).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 field) ^ 2
        ∂BranchingProcess.offspringFieldLaw
          (μ.map (Step.selectFamily {ξ | totalPotentialWeight φ (-1) ξ ≤ K}))) ≤
      K * ENNReal.ofReal (Real.exp (3 * D ^ v + 2 * U - 2 * d * (N - 1) / D ^ 2)) *
        (∑ m : Fin N, ENNReal.ofReal (Real.exp
          (d * (m.val : ℝ) / D ^ 2 - (lower + c / D ^ 2 * (m.val : ℝ))))) +
        ENNReal.ofReal (Real.exp (U + D ^ v - d * N / D ^ 2)) :=
  exists_lintegral_pathGeneration_affineCorridor_sq_le_cutoff_mul_exp_sum_of_finiteVariance
    φ μ hb hν hvar hv hc hd hcrit

#print axioms ProbabilityTheory.Kernel.runPartialSteps_comp_noise
#print axioms ProbabilityTheory.Kernel.ofPartialStep_map_noise
#print axioms ProbabilityTheory.Kernel.measurable_restrictNoise
#print axioms ProbabilityTheory.Kernel.runPartialSteps_restrictNoise
#print axioms ProbabilityTheory.Kernel.endsInPrefix_restrictNoise_iff
#print axioms ProbabilityTheory.Kernel.survivesPrefix_restrictNoise_iff
#print axioms ProbabilityTheory.Kernel.eventually_pow_le_survival_restrictNoise
#print axioms ProbabilityTheory.RandomWalk.endsInPrefix_killedStep_iff
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.killedMarkedStep_measurable
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.survivesPrefix_killedMarkedStep_iff
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.survivesPrefix_restrictNoise_killedMarkedStep_iff
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.endsInPrefix_killedMarkedStep_iff
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.measurableSet_corridorEvent
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Marked.eventually_affineCorridorProbability_ge_exp_of_finiteVariance
#print axioms Combinatorics.Branching.Step.selectFamily_measurable
#print axioms Combinatorics.Branching.surviveAlong_selectFamily_iff
#print axioms Combinatorics.Branching.displaceWith_selectFamily_eq_of_survive
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathGeneration_selectFamily_le
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathHistory_selectFamily_eq_of_survive
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathGenerationTerm_selectFamily_eq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathGeneration_selectFamily_eq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.offspringFieldLaw_map_selectFamily
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_selectFamily_le
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_crossPotentialWeight_selectFamily_eq_restrict
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution_selectFamily_le
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_pathGeneration_affineCorridor_sq_eq_firstMoment_add_mrcaContributions
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_selectFamily_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_cutoff_mul_exp_sum_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance

#print axioms Asymptotics.tendsto_succ_quotientBlockCount_mul_scale_div

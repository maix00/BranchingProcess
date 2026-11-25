import Probability.BranchingRandomWalk.Spine.Tube.Corridor.FamilySelection
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Identity

open MeasureTheory ProbabilityTheory Combinatorics.Branching Filter
open ProbabilityTheory.BranchingRandomWalk ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open scoped ENNReal Topology Classical

-- The rejected family at the child is inspected only when the child
-- reproduces. It contributes one particle at time one and none at time two.
example :
    let field : StepField ℕ ℝ := fun u i =>
      if u = [] then (if i = 0 then some 0 else none)
      else if i ≤ 1 then some 0 else none
    let A : Set (Step ℕ ℝ) := {ξ | ξ 1 = none}
    pathGeneration realPotential 1 (fun _ => 1) 0 (fun u => Step.selectFamily A (field u)) = 1 ∧
      pathGeneration realPotential 2 (fun _ => 1) 0 (fun u => Step.selectFamily A (field u)) = 0 := by
  simp [pathGeneration_succ, pathGeneration_zero, Step.selectFamily, survive,
    survivingPotentialTest, subtreeStepField]

-- The actual truncated process has positive corridor mean under the weak
-- spinal tail condition alone; no finite untruncated cross moment is available.
example {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {σ α d : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) (σ ^ 2))
    (hσ : 0 < σ) (htail : HasSpinalWeightTail φ μ) (hα : 0 < α)
    (hd : (Real.pi ^ 2 / 2) * σ ^ 2 < d)
    {L : ℕ → ℝ} {H : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hH : ∀ᶠ n in atTop, 0 < H n)
    (hsmall : Tendsto (fun n => L n ^ 2 / (H n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 <
      ∫⁻ field, pathGeneration φ (H n)
        ((affineCorridorThrough (H n) (-(L n / 2)) 0 (L n) (L n / 8)).indicator
          (fun _ => (1 : ℝ≥0∞))) 0 field
        ∂BranchingProcess.offspringFieldLaw (μ.map (Step.selectFamily
          {ξ | totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp (α * L n))})) := by
  have h := eventually_lintegral_pathGeneration_affineCorridor_cutoff_ge_of_finiteVariance
    (c := 0) (a := 0) (b := 0) (ρ := 1 / 8) φ μ hboundary hcentered hσ htail
    (by norm_num) hα hd (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hL hH hsmall
  filter_upwards [h] with n hn
  have hp : 0 < ENNReal.ofReal (Real.exp
      ((0 - 1 / 8 - 0) * L n + (0 - d) * (H n : ℝ) / L n ^ 2)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  simpa [div_eq_mul_inv, mul_comm] using hp.trans_le hn

#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathGeneration_eq_tsum_fin
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathManyToOne_selectFamily
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathManyToOneCore
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.weightedPathManyToOneCore
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathManyToOne
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.weightedPathManyToOne
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.eventually_lintegral_pathGeneration_affineCorridor_cutoff_ge_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.eventually_measure_hasPathHistoryIn_affineCorridor_cutoff_ge_of_finiteVariance

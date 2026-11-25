import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Sequence.UpperTail.SpinalWeight
import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Survival
import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.FamilySelection

open MeasureTheory ProbabilityTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.Process.Path
open scoped ENNReal Classical

-- At horizon zero the initial root is the successful terminal particle.
-- This uses only finite family weight, and admits laws with empty offspring;
-- boundary normalization, positive variance and nonextinction are absent.
example (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hweight : ∀ᵐ ξ ∂μ, totalPotentialWeight realPotential (-1) ξ ≠ ∞) :
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin 1 => (0 : ℝ)) realPotential realPotential.measurable_toFun
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin 1)))
      (by simp [RootIndexed.mem_initialPopulation_iff]) 0
      (fun _ => Set.Icc (-1 : ℝ) 1) (fun _ => measurableSet_Icc)
      (fun _ => 1) (fun _ _ h => h.2)
    finiteRootStepFieldLaw μ 1 {field | ¬ ∃ p ∈ P 0 field,
      RootIndexed.position (fun _ : Fin 1 => 0) realPotential field p.1 p.2 = 0} ≤
      ENNReal.ofReal (Real.exp (-1)) := by
  let C : Set (Fin 1 → ℝ) := {path | path 0 = 0}
  have hC : MeasurableSet C := measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have hevent : hasPathHistoryIn (ι := ℕ) realPotential 0 0 C = Set.univ := by
    ext field
    simp only [Set.mem_univ, iff_true]
    exact ⟨[], rfl, trivial, by simp [C, pathHistory]⟩
  have hprob : (1 : ℝ) ≤ (BranchingProcess.offspringFieldLaw μ).real
      (hasPathHistoryIn (ι := ℕ) realPotential 0 0 C) := by
    rw [hevent]
    simp
  have h := RootIndexed.CausalPopulation.measure_terminalPosition_avoidance_le_exp_of_pathSuccess
    realPotential μ hweight 1 0 0 (fun _ => Set.Icc (-1 : ℝ) 1)
    (fun _ => measurableSet_Icc) (fun _ => 1) (fun _ _ h => h.2) C hC
    (fun path _ hz k => by
      have hk : k = 0 := by apply Fin.ext; omega
      subst k
      simp [restartAnchor, hz])
    ({0} : Set ℝ) (fun path hp => by simpa [C] using hp) 1 (by norm_num) le_rfl hprob
  simpa only [Nat.cast_one, neg_mul, one_mul, Set.mem_singleton_iff] using h

#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.lintegral_size_le_sum_pathGeneration_restartedWindow
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.measure_hasPathHistoryIn_selectFamily_le
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.eventually_exp_le_measure_hasPathHistoryIn_affineCorridor_of_cubicScale
#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.exists_measure_capacityEvent_compl_affine_selectFamily_le_exp_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.measure_terminalPosition_avoidance_le_exp_of_pathSuccess
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.measure_endpointMinimum_gt_le_terminalAvoidance_add_capacityFailure
#print axioms ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.eventually_measure_endpointMinimum_gt_le_affineBudget_of_spinalWeightTail

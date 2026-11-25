/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.FirstMoment
public import Probability.BranchingRandomWalk.Spine.Tube.Corridor.FirstMoment.FamilySelection

/-!
# Finite-root affine-corridor capacity after whole-family selection

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.exists_measure_capacityEvent_compl_affine_selectFamily_le_exp_of_finiteVariance`:
  under original boundary normalization and centered spinal variance `σ²>0`,
  for `c≥0`, `0<d<π²σ²/2`, large real `L`, `lower∈[-L,0]` and any
  measurable family event `A`, the actual relative affine-corridor population
  from roots `R` under `μA=μ.map(selectFamily A)` satisfies
  `P_μA(Cap(N,H)ᶜ) ≤ |R|(H+1)exp(lower+L+√L+max(c-d,0)H/L²)/(N+1)`.
  The threshold is uniform in `A`, the roots, their initial positions, `H`
  and `N`. No weak-tail or cross-weight assumption is required.

The population, capacity event, field law and root marginal integration are
existing interfaces. Only the original spine is centered and normalized.
The proof uses the cumulative actual selected count and the existing Markov
capacity inequality. It extends the population-budget argument in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, proof of Theorem 1.1, to whole-family
selection. The random-walk upper bound is Chapter 3, Lemma 3.4.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

private lemma pathGeneration_affine_restarted_eq
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (lower slope width x : ℝ) (field : Combinatorics.Branching.StepField ι X) :
    pathGeneration φ n
      (restartedWindowTest 0 (fun j => Set.Icc (lower + slope * (j : ℝ))
        (lower + slope * (j : ℝ) + width))) x field =
      pathGeneration φ n ((affineCorridorPrefix n lower slope width).indicator
        (fun _ => (1 : ℝ≥0∞))) 0 field := by
  apply tsum_congr
  intro u
  unfold pathGenerationTerm
  by_cases hu : u.length = n ∧ surviveAlong field [] u
  · have hmem : field ∈ {ω | u.length = n ∧ surviveAlong ω [] u} := hu
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    have hevent : InRestartedWindows 0
        (fun j => Set.Icc (lower + slope * (j : ℝ)) (lower + slope * (j : ℝ) + width))
        (pathHistory φ n x field u) ↔
        pathHistory φ n 0 field u ∈ affineCorridorPrefix n lower slope width := by
      simp [InRestartedWindows, restartAnchor, pathHistory, affineCorridorPrefix]
    simp only [restartedWindowTest, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [hevent]
  · have hmem : field ∉ {ω | u.length = n ∧ surviveAlong ω [] u} := hu
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- The finite-root capacity budget after arbitrary measurable whole-family
selection. This extends the population estimate in Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 4, proof of Theorem 1.1, using Chapter 3, Lemma 3.4. -/
theorem exists_measure_capacityEvent_compl_affine_selectFamily_le_exp_of_finiteVariance
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) {variance c d : ℝ}
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ) variance)
    (hvariance : 0 < variance) (hc : 0 ≤ c) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ A : Set (Step ι X), MeasurableSet A →
      ∀ lower : ℝ, -L ≤ lower → lower ≤ 0 →
      ∀ {Root : Type*} [MeasurableSpace (RootIndexed.TreeNode Root ι)]
      [Countable (RootIndexed.TreeNode Root ι)], ∀ (roots : Finset Root) (initialPosition : Root → ℝ) (N H : ℕ),
      let window := fun j : ℕ => Set.Icc (lower + c / L ^ 2 * (j : ℝ))
        (lower + c / L ^ 2 * (j : ℝ) + L)
      let P := ofRestartedRealPositionSets initialPosition φ φ.measurable_toFun
        (RootIndexed.initialPopulation (α := ι) roots)
        (by simp [RootIndexed.mem_initialPopulation_iff]) 0 window
        (fun _ => measurableSet_Icc) (fun j => lower + c / L ^ 2 * (j : ℝ) + L)
        (fun _ _ h => h.2)
      RootIndexed.stepFieldLaw (Root := Root) (μ.map (Step.selectFamily A))
        (P.capacityEvent N H)ᶜ ≤
        (roots.card : ℝ≥0∞) * ((H : ℝ≥0∞) + 1) * ENNReal.ofReal (Real.exp
          (lower + L + L ^ (1 / 2 : ℝ) + max (c - d) 0 * (H : ℝ) / L ^ 2)) /
          (N + 1 : ℕ) := by
  obtain ⟨L₀, hL₀, hmean⟩ :=
    exists_lintegral_sum_pathGeneration_affineCorridorPrefix_selectFamily_le_exp_of_finiteVariance
      φ μ hboundary hcentered hvariance hc hd hcritical
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL A hA lower hlower hupper Root _ _ roots initialPosition N H window P
  let μA := μ.map (Step.selectFamily A)
  let : IsProbabilityMeasure μA :=
    (Measure.isProbabilityMeasure_map_iff (Step.selectFamily_measurable hA).aemeasurable).2 inferInstance
  let I j := ∫⁻ field, pathGeneration φ j
    ((affineCorridorPrefix j lower (c / L ^ 2) L).indicator (fun _ => (1 : ℝ≥0∞))) 0 field
    ∂ProbabilityTheory.BranchingProcess.offspringFieldLaw μA
  have hsize (j : ℕ) :
      (∫⁻ field, P.size j field ∂RootIndexed.stepFieldLaw (Root := Root) μA) ≤
        (roots.card : ℝ≥0∞) * I j := by
    have h := lintegral_size_le_sum_pathGeneration_restartedWindow roots initialPosition
      φ φ.measurable_toFun μA 0 window (fun _ => measurableSet_Icc)
      (by dsimp [window]; constructor <;> simp only [Nat.cast_zero, mul_zero, add_zero] <;> linarith)
      (fun j => lower + c / L ^ 2 * (j : ℝ) + L) (fun _ _ h => h.2) j
    dsimp [window] at h
    simp_rw [pathGeneration_affine_restarted_eq] at h
    simpa [I, nsmul_eq_mul] using h
  have hsum : (∑ j : Fin (H + 1), I j.val) ≤ ((H : ℝ≥0∞) + 1) *
      ENNReal.ofReal (Real.exp
        (lower + L + L ^ (1 / 2 : ℝ) + max (c - d) 0 * (H : ℝ) / L ^ 2)) := by
    have h := hmean L hL A hA lower hlower hupper H
    rw [lintegral_finsetSum' Finset.univ (fun j _ =>
      (pathGeneration_measurable φ j.val
        (measurable_const.indicator (measurableSet_affineCorridorPrefix _ _ _ _)) 0).aemeasurable)] at h
    exact h
  refine (P.measure_capacityEvent_compl_le_lintegral
    (RootIndexed.stepFieldLaw (Root := Root) μA) N H (fun j =>
      (RootIndexed.stepFiltration (Root := Root) (α := ι) (X := X)).le j)).trans ?_
  calc
    _ ≤ ∑ j : Fin (H + 1), ((roots.card : ℝ≥0∞) * I j.val) / (N + 1 : ℕ) := by
      exact Finset.sum_le_sum (fun j _ => ENNReal.div_le_div_right (hsize j.val) _)
    _ = ((roots.card : ℝ≥0∞) * ∑ j : Fin (H + 1), I j.val) / (N + 1 : ℕ) := by
      simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := by
      exact ENNReal.div_le_div_right (by simpa only [mul_assoc] using
        (mul_le_mul' (le_refl (roots.card : ℝ≥0∞)) hsum)) _

end ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Analytic.LeftTailAtAOne
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Selected-population transfer for endpoint paths with bounded drawdown

At a fixed generation, every particle retained by first-`N` selection is an
actual surviving vertex of one of the initial root trees.  Thus the event
that a retained particle has a low endpoint and no large ancestral drawdown
is contained in the union of the corresponding one-root branching events.
The existing many-to-one estimate then gives the selected-population bound.
This is only the no-large-drawdown term in Aïdékon--Hu's estimate (4.16); the
large-drawdown exceptional event is a separate estimate.
-/

section

attribute [local instance] Classical.propDecidable Classical.decEq

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- The generation-`n` population produced by totalized first-`N`
selection from `m` independent initial roots, all started at zero.  The
totalized selector is empty off the lower-finite domain, so no nonempty
offspring assumption is built into this definition. -/
noncomputable def firstNSelectedPopulation (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ) :
    Finset (RootIndexed.TreeNode (Fin m) ℕ) := by
  classical
  exact RootIndexed.selectedPopulationTotalized N
    (Finset.univ : Finset (Fin m)) (fun _ => 0) id id n field

/-- A selected generation-`n` particle has endpoint at most `threshold` and
its ancestral path has no downward drawdown larger than `delta`.  The event
is phrased by an actual selected address, so it is false when the selected
population is empty. -/
def firstNSelectedNoLargeDropEndpointBelow (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) : Set (FiniteRootStepField m ℕ ℝ) :=
  {field | ∃ p : RootIndexed.TreeNode (Fin m) ℕ,
    p ∈ firstNSelectedPopulation m N n field ∧
      p.2.length = n ∧
      surviveAlong (field p.1) [] p.2 ∧
      historyNoLargeDropAndEndpointBelow delta threshold
        (Spine.pathHistory realPotential n 0 (field p.1) p.2)}

theorem firstNSelectedPopulation_measurable (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable (firstNSelectedPopulation m N n) := by
  classical
  have hflow : Measurable[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) n]
      (firstNSelectedPopulation m N n) := by
    exact RootIndexed.selectedPopulationTotalized_adapted
      N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id
      measurable_id id measurable_id n
  exact hflow.mono
    (Filtration.le (RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ)) n)
    le_rfl

theorem measurableSet_firstNSelectedNoLargeDropEndpointBelow
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) :
    MeasurableSet
      (firstNSelectedNoLargeDropEndpointBelow m N n delta threshold) := by
  have hpopulation : Measurable (firstNSelectedPopulation m N n) :=
    firstNSelectedPopulation_measurable m N n
  rw [show firstNSelectedNoLargeDropEndpointBelow m N n delta threshold =
      ⋃ p : RootIndexed.TreeNode (Fin m) ℕ,
        {field | p ∈ firstNSelectedPopulation m N n field ∧
          p.2.length = n ∧
          surviveAlong (field p.1) [] p.2 ∧
          historyNoLargeDropAndEndpointBelow delta threshold
            (Spine.pathHistory realPotential n 0 (field p.1) p.2)} by
    ext field
    simp [firstNSelectedNoLargeDropEndpointBelow]]
  apply MeasurableSet.iUnion
  intro p
  have hmem : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        p ∈ firstNSelectedPopulation m N n field} :=
    hpopulation (measurableSet_mem_finset p)
  have hdepth : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ | p.2.length = n} := by
    by_cases hp : p.2.length = n <;> simp [hp]
  have hpath : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} :=
    (measurableSet_historyNoLargeDropAndEndpointBelow delta threshold).preimage
      ((Spine.pathHistory_measurable realPotential n 0 p.2).comp
        (measurable_pi_apply p.1))
  have hsurvive : MeasurableSet
      {field : FiniteRootStepField m ℕ ℝ |
        surviveAlong (field p.1) [] p.2} :=
    (Spine.measurableSet_surviveAlong [] p.2).preimage
      (measurable_pi_apply p.1)
  rw [show {field : FiniteRootStepField m ℕ ℝ |
      p ∈ firstNSelectedPopulation m N n field ∧
        p.2.length = n ∧
        surviveAlong (field p.1) [] p.2 ∧
        historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} =
      {field | p ∈ firstNSelectedPopulation m N n field} ∩
        {field | p.2.length = n} ∩
        {field | surviveAlong (field p.1) [] p.2} ∩
        {field | historyNoLargeDropAndEndpointBelow delta threshold
          (Spine.pathHistory realPotential n 0 (field p.1) p.2)} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]]
  exact ((hmem.inter hdepth).inter hsurvive).inter hpath

theorem firstNSelectedPopulation_depth (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N n field) :
    p.2.length = n :=
  by
    classical
    change p ∈ RootIndexed.selectedPopulationTotalized N
      (Finset.univ : Finset (Fin m)) (fun _ : Fin m => (0 : ℝ)) id id n field
      at hp
    exact RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      (fun _ : Fin m => (0 : ℝ)) id id n field p hp

/-- First-`N` selection never introduces a particle whose ancestral path
contains an absent child. The induction follows the actual parent/child
presentation of `childrenAtGeneration`; the empty-offspring case contributes
no selected address. -/
theorem firstNSelectedPopulation_surviveAlong (m N n : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : FiniteRootStepField m ℕ ℝ)
    (p : RootIndexed.TreeNode (Fin m) ℕ)
    (hp : p ∈ firstNSelectedPopulation m N n field) :
    surviveAlong (field p.1) [] p.2 := by
  classical
  induction n generalizing p with
  | zero =>
      simp only [firstNSelectedPopulation, RootIndexed.selectedPopulationTotalized]
        at hp
      rw [RootIndexed.initialPopulation, Finset.mem_map] at hp
      obtain ⟨r, _, rfl⟩ := hp
      exact surviveAlong_nil _ []
  | succ n ih =>
      change p ∈ RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ : Fin m => (0 : ℝ)) id id
        (n + 1) field at hp
      have hchild := RootIndexed.selectedPopulationTotalized_succ_subset
        N (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field hp
      obtain ⟨q, hq, hqdepth, i, hi, rfl⟩ :=
        (RootIndexed.mem_childrenAtGeneration_iff n
          (firstNSelectedPopulation m N n field) field p).mp hchild
      exact (surviveAlong_append_singleton (field q.1) [] q.2 i).2
        ⟨ih q hq, hi⟩

/-- The no-large-drawdown event for a retained endpoint is contained in the
union of the corresponding one-root events in the full pre-sampled forest.
This containment is pathwise and does not use a branching-property
assumption or a nonempty-offspring premise. -/
theorem firstNSelectedNoLargeDropEndpointBelow_subset_roots
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ) :
    firstNSelectedNoLargeDropEndpointBelow m N n delta threshold ⊆
      ⋃ r : Fin m,
        {field : FiniteRootStepField m ℕ ℝ |
          field r ∈ hasNoLargeDropEndpointBelow realPotential n delta threshold} := by
  intro field hfield
  obtain ⟨p, hp, hdepth, hsurvive, hpath⟩ := hfield
  refine Set.mem_iUnion.2 ⟨p.1, ?_⟩
  change field p.1 ∈ hasNoLargeDropEndpointBelow realPotential n delta threshold
  exact ⟨p.2, hdepth, hsurvive, hpath⟩

/-- Fixed-generation selected-population transfer of the endpoint/no-large-
drawdown event.  The proof is full-branching containment followed by a union
bound over the `m` initial roots and the existing one-root many-to-one
estimate.  This closes only the second (no-large-drawdown) term in the proof
of Aïdékon--Hu (4.16); it does not estimate the large-drawdown event. -/
theorem measure_firstNSelectedNoLargeDropEndpointBelow_le
    (m N n : ℕ) [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (delta threshold : ℝ)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    (finiteRootStepFieldLaw μ m)
        (firstNSelectedNoLargeDropEndpointBelow m N n delta threshold) ≤
      (m : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp threshold) *
          (tiltedIncrementFieldLaw realPotential μ)
            (spineNoLargeDropEndpointBelowEvent n delta threshold)) := by
  let E : Set (FiniteRootStepField m ℕ ℝ) :=
    firstNSelectedNoLargeDropEndpointBelow m N n delta threshold
  let A : Set (StepField ℕ ℝ) :=
    hasNoLargeDropEndpointBelow realPotential n delta threshold
  have hsubset : E ⊆ ⋃ r : Fin m, {field : FiniteRootStepField m ℕ ℝ |
      field r ∈ A} := by
    exact firstNSelectedNoLargeDropEndpointBelow_subset_roots m N n delta threshold
  have hroot (r : Fin m) :
      (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ ℝ | field r ∈ A} =
        (stepFieldLaw μ) A := by
    change (finiteRootStepFieldLaw μ m)
      ((fun field : FiniteRootStepField m ℕ ℝ => field r) ⁻¹' A) = _
    rw [← Measure.map_apply (measurable_pi_apply r)
      (measurableSet_hasNoLargeDropEndpointBelow realPotential n delta threshold)]
    rw [finiteRootStepFieldLaw_root_marginal μ r]
  have honeRoot :=
    measure_hasNoLargeDropEndpointBelow_le_exp_mul_spineProbability
      realPotential μ hboundary n delta threshold
  calc
    (finiteRootStepFieldLaw μ m) E ≤
        (finiteRootStepFieldLaw μ m)
          (⋃ r : Fin m, {field : FiniteRootStepField m ℕ ℝ | field r ∈ A}) :=
      measure_mono hsubset
    _ ≤ ∑ r : Fin m,
          (finiteRootStepFieldLaw μ m)
            {field : FiniteRootStepField m ℕ ℝ | field r ∈ A} :=
      measure_iUnion_fintype_le (finiteRootStepFieldLaw μ m) _
    _ ≤ ∑ _r : Fin m,
          ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent n delta threshold) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [hroot r]
      exact honeRoot
    _ = (m : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp threshold) *
            (tiltedIncrementFieldLaw realPotential μ)
              (spineNoLargeDropEndpointBelowEvent n delta threshold)) := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

end ProbabilityTheory.BranchingRandomWalk.Analytic

end

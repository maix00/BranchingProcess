/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Endpoint
set_option linter.style.haveILetI false

/-!
# Endpoint sublevel probabilities for nested root sets

The rank-installed coupling shows that adding initial roots can only increase
the probability of finding a selected endpoint below a fixed threshold.  The
two fields in the coupling have the same product-law marginal, so this
pathwise comparison transfers to their endpoint probabilities.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- There is a generation-`n` particle in first-`N` selection from `roots`
whose position is at most `threshold`. -/
def RootIndexed.selectedPopulationEndpointBelow
    {Root α : Type*} [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (n : ℕ) (threshold : ℝ) :
    Set (RootIndexed.StepField Root α ℝ) :=
  {field | ∃ p : RootIndexed.TreeNode Root α,
    p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field ∧
      RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold}

theorem measurableSet_RootIndexed_selectedPopulationEndpointBelow
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (n : ℕ) (threshold : ℝ) :
    MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N roots initialPosition n threshold) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) :=
    fun a b => LinearOrder.toDecidableEq a b
  rw [show RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
      N roots initialPosition n threshold =
      ⋃ p : RootIndexed.TreeNode Root α,
        {field | p ∈ RootIndexed.selectedPopulationTotalized N roots
          initialPosition id id n field ∧
          RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} by
    ext field
    simp only [RootIndexed.selectedPopulationEndpointBelow,
      Set.mem_ofPred_eq, Set.mem_iUnion]]
  apply MeasurableSet.iUnion
  intro p
  have hpopulation : Measurable
      (RootIndexed.selectedPopulationTotalized (Root := Root) (α := α)
        (Mark := ℝ) (Position := ℝ) (Value := ℝ)
        N roots initialPosition id id n) := by
    exact (RootIndexed.selectedPopulationTotalized_adapted
      (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
      N roots initialPosition id measurable_id id measurable_id n).mono
        (Filtration.le
          (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) n)
        le_rfl
  have hmem : MeasurableSet
      {field : RootIndexed.StepField Root α ℝ |
        p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field} :=
    hpopulation (measurableSet_mem_finset p)
  have hposition : Measurable
      (fun field : RootIndexed.StepField Root α ℝ =>
        RootIndexed.position initialPosition id field p.1 p.2) := by
    exact (RootIndexed.position_measurable initialPosition id measurable_id p.1 p.2).mono
      (Filtration.le
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)) p.2.length)
      le_rfl
  have hbelow : MeasurableSet
      {field : RootIndexed.StepField Root α ℝ |
        RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} :=
    measurableSet_Iic.preimage hposition
  rw [show {field : RootIndexed.StepField Root α ℝ |
      p ∈ RootIndexed.selectedPopulationTotalized N roots initialPosition id id n field ∧
        RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} =
      {field | p ∈ RootIndexed.selectedPopulationTotalized N roots
        initialPosition id id n field} ∩
      {field | RootIndexed.position initialPosition id field p.1 p.2 ≤ threshold} by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]]
  exact hmem.inter hbelow

/-- Under boundary normalization, the endpoint-sublevel probability for a
larger finite root set is at least that for a contained root set.  This is the
law-level form of the nested-root rank-installed coupling. -/
theorem RootIndexed.measure_selectedPopulationEndpointBelow_mono_roots
    {Root α : Type*} [Countable Root] [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (sourceRoots targetRoots : Finset Root)
    (hroots : sourceRoots ⊆ targetRoots)
    (initialPosition : Root → ℝ) (n : ℕ) (threshold : ℝ) :
    (RootIndexed.stepFieldLaw (Root := Root) μ)
        (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N sourceRoots
          initialPosition n threshold) ≤
      (RootIndexed.stepFieldLaw (Root := Root) μ)
        (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N targetRoots
          initialPosition n threshold) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) :=
    fun a b => LinearOrder.toDecidableEq a b
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let μRoot := RootIndexed.stepFieldLaw (Root := Root) μ
  let left : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField Root α ℝ := RootIndexed.StepField.left
  let source := RootIndexed.selectedPopulationTotalizedSource
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N sourceRoots initialPosition id measurable_id id measurable_id
  let sourceFinite := RootIndexed.selectedPopulationTotalizedSource_finiteSlices
    (Root := Root) (α := α) (Mark := ℝ) (Position := ℝ) (Value := ℝ)
    N sourceRoots initialPosition id measurable_id id measurable_id
  have hsourceEq : sourceFinite.toFinset =
      (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
        initialPosition id id k (RootIndexed.StepField.left field)) := by
    funext k
    funext field
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    change (source.toPopulation field).particles k = _
    rfl
  let targetField := RootIndexed.restartedRealPositionMatchedField N targetRoots
    initialPosition id sourceFinite.toFinset n
  have hleftMeasurable : Measurable left := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    rw [measurable_pi_iff]
    intro r
    rw [measurable_pi_iff]
    intro u
    exact (measurable_pi_apply u).comp (measurable_pi_apply (Sum.inl r))
  have hleftLaw : P.map left = μRoot := by
    change (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.reindex Sum.inl) = _
    exact RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hleftSet : MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N sourceRoots initialPosition
        n threshold) :=
    measurableSet_RootIndexed_selectedPopulationEndpointBelow
      (Root := Root) (α := α) N sourceRoots initialPosition n threshold
  have htargetSet : MeasurableSet
      (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N targetRoots initialPosition
        n threshold) :=
    measurableSet_RootIndexed_selectedPopulationEndpointBelow
      (Root := Root) (α := α) N targetRoots initialPosition n threshold
  have htargetLaw : Measurable targetField ∧ P.map targetField = μRoot := by
    change Measurable
        (RootIndexed.restartedRealPositionMatchedField N targetRoots initialPosition id
          sourceFinite.toFinset n) ∧
      P.map (RootIndexed.restartedRealPositionMatchedField N targetRoots
        initialPosition id sourceFinite.toFinset n) = μRoot
    have hleft : RootIndexed.StepField.left =
        (RootIndexed.StepField.reindex Sum.inl :
          RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ) := rfl
    simpa only [P, μRoot, RootIndexed.restartedRealPositionMatchedField, hleft] using
      (RootIndexed.rankInstalledField_causalPopulation_measurable_law
        μ N targetRoots initialPosition id measurable_id id measurable_id
        source sourceFinite n)
  have hsourceMarginal : P (left ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N sourceRoots initialPosition
        n threshold) =
      μRoot (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N sourceRoots
        initialPosition n threshold) := by
    rw [← hleftLaw, Measure.map_apply hleftMeasurable hleftSet]
  have htargetMarginal : P (targetField ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N targetRoots initialPosition
        n threshold) =
      μRoot (RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N targetRoots
        initialPosition n threshold) := by
    rw [← htargetLaw.2, Measure.map_apply htargetLaw.1 htargetSet]
  have hcoupled := RootIndexed.selectedPopulationNestedRoots_endpointBelow_ae
    μ hboundary N sourceRoots targetRoots hroots initialPosition n threshold
  have hsubset : ∀ᵐ field ∂P,
      field ∈ left ⁻¹'
          RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N sourceRoots
            initialPosition n threshold →
        field ∈ targetField ⁻¹'
          RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α) N targetRoots
            initialPosition n threshold := by
    filter_upwards [hcoupled] with field hcoupled
    intro hsource
    have hsource' : ∃ p : RootIndexed.TreeNode Root α,
        p ∈ RootIndexed.selectedPopulationTotalized N sourceRoots
          initialPosition id id n (RootIndexed.StepField.left field) ∧
        RootIndexed.position initialPosition id (RootIndexed.StepField.left field)
          p.1 p.2 ≤ threshold := by
      simpa [left, RootIndexed.selectedPopulationEndpointBelow] using hsource
    rcases hcoupled hsource' with ⟨q, hq, hqx⟩
    have htarget : ∃ q : RootIndexed.TreeNode Root α,
        q ∈ RootIndexed.restartedRealPositionMatchedPopulation N targetRoots
          initialPosition id
          (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
            initialPosition id id k (RootIndexed.StepField.left field)) n field ∧
        RootIndexed.position initialPosition id
          (RootIndexed.restartedRealPositionMatchedField N targetRoots
            initialPosition id
            (fun k field => RootIndexed.selectedPopulationTotalized N sourceRoots
              initialPosition id id k (RootIndexed.StepField.left field)) n field)
          q.1 q.2 ≤ threshold := ⟨q, hq, hqx⟩
    simpa [targetField, RootIndexed.restartedRealPositionMatchedPopulation,
      RootIndexed.restartedRealPositionMatchedField,
      RootIndexed.selectedPopulationEndpointBelow, hsourceEq] using htarget
  have hmeasure : P (left ⁻¹'
      RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
        N sourceRoots initialPosition
        n threshold) ≤
      P (targetField ⁻¹'
        RootIndexed.selectedPopulationEndpointBelow (Root := Root) (α := α)
          N targetRoots initialPosition
          n threshold) := by
    exact measure_mono_ae hsubset
  rw [hsourceMarginal, htargetMarginal] at hmeasure
  simpa [μRoot] using hmeasure

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

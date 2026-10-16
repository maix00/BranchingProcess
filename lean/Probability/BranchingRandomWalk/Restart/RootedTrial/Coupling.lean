/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Restarted
import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# N-selection comparison for the causal reserve source

This file connects the concrete pre-sampled reserve spine and its fixed
cap-stopped candidate windows to the existing first-`N` rank-installation
coupling. Candidate activation is determined by the reserve spine alone;
it never depends on earlier candidate outcomes.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- Pull the one-root causal reserve source back to the left half of the
common pre-sampled field used by the N-selection rank-installation coupling. -/
noncomputable def selectedReserveSpineRestartSourceOnLeft
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left := by
  let P := selectedReserveSpineRestartSource R growth hR hgrowth cap duration r
  have hleft : ∀ k, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (RootIndexed.StepField Root α ℝ)
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) k)
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ) k)
      RootIndexed.StepField.left := by
    intro k
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ)
      by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable Sum.inl k
  exact P.pullback RootIndexed.StepField.left hleft rfl

/-- The left-field version inherits layerwise finiteness from the finite
union representation of the reserve source. -/
theorem selectedReserveSpineRestartSourceOnLeft_finiteSlices
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root) :
    (selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
      cap duration r).FiniteSlices := by
  let P := selectedReserveSpineRestartSource R growth hR hgrowth cap duration r
  have hP := selectedReserveSpineRestartSource_finiteSlices R growth hR hgrowth
    cap duration r
  have hleft : ∀ k, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (RootIndexed.StepField Root α ℝ)
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) k)
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ) k)
      RootIndexed.StepField.left := by
    intro k
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α ℝ → RootIndexed.StepField Root α ℝ)
      by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable Sum.inl k
  exact hP.pullback RootIndexed.StepField.left hleft rfl

/-- The finite source slice on the left copy is the original reserve-source
slice evaluated on that copy. -/
theorem selectedReserveSpineRestartSourceOnLeft_toFinset
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root)
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
    let hleft := selectedReserveSpineRestartSourceOnLeft_finiteSlices
      R growth hR hgrowth cap duration r
    let hsource := selectedReserveSpineRestartSource_finiteSlices
      R growth hR hgrowth cap duration r
    hleft.toFinset n field = hsource.toFinset n (RootIndexed.StepField.left field) := by
  apply Finset.coe_injective
  simp [selectedReserveSpineRestartSourceOnLeft,
    RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset,
    RootIndexed.CausalPopulation.pullback_population]

/-- The source-plus-window population has the explicit pathwise capacity
`1 + (duration + 1) * (2 * cap)`. -/
theorem selectedReserveSpineRestartSourceOnLeft_card_le
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ)
    (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap) (r : Root)
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
    ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
      cap duration r).toFinset n field).card ≤ 1 + (duration + 1) * (2 * cap) := by
  rw [selectedReserveSpineRestartSourceOnLeft_toFinset]
  exact selectedReserveSpineRestartSource_card_le R growth hR hgrowth cap duration
    hbounded hcap r (selectedReserveSpineRestartSource_finiteSlices
      R growth hR hgrowth cap duration r) n (RootIndexed.StepField.left field)

/-- Initial source injection for the singleton-root reserve source. -/
noncomputable def selectedReserveSpineRestartSourceOnLeft_initialInjection
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root)
    (N : ℕ)
    (initialPosition : Root → ℝ)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
    Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
          hgrowth cap duration r).toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.selectedPopulationTotalized N {r} initialPosition id id 0
          (RootIndexed.StepField.right field))) () := by
  let hleft := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth cap duration r
  have hzero : hleft.toFinset 0 field = RootIndexed.initialPopulation (α := α) {r} := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rw [selectedReserveSpineRestartSourceOnLeft, RootIndexed.CausalPopulation.pullback_population]
    ext q
    change q ∈ selectedReserveSpineRestartSourceSlice R growth hR cap duration r 0
        (RootIndexed.StepField.left field) ↔
      q ∈ RootIndexed.initialPopulation (α := α) {r}
    rw [RootIndexed.mem_initialPopulation_iff]
    simp [selectedReserveSpineRestartSourceSlice,
      selectedReserveSpineCandidatePopulation, selectedReserveSpineCandidateEnabled,
      Concurrent.Finite.population, Concurrent.Finite.component,
      selectedReserveSpineAlive, selectedReserveSpinePath]
  rw [hzero]
  simpa [RootIndexed.selectedPopulationTotalized] using
    (RootIndexed.initialPopulationInjection id id {r} initialPosition
      (RootIndexed.StepField.left field) (RootIndexed.StepField.right field))

/-- Concrete almost-sure rank-installation coupling for the reserve spine
and all fixed-window candidate trials. Its only pathwise capacity premise is
the deterministic finite-window bound; candidate success is not used to
define the source. -/
theorem selectedReserveSpineRestartCoupledInjection_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (cap duration : ℕ) (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (hcapacity : 1 + (duration + 1) * (2 * cap) ≤ N)
    (r : Root) (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      Nonempty (Cloud.SliceDominatingMap id
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field))
          ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
            hgrowth cap duration r).toFinset n field))
        (Combinatorics.Branching.Selection.Coupling.populationCloud id
          (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
              (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                hgrowth cap duration r).toFinset n field))
          (RootIndexed.restartedRealPositionMatchedPopulation N {r} initialPosition id
            (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
              hgrowth cap duration r).toFinset n field)) ()) := by
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth cap duration r
  have hsource : source.FiniteSlices := by
    dsimp [source]
    exact selectedReserveSpineRestartSourceOnLeft_finiteSlices
      R growth hR hgrowth cap duration r
  have hinitial : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsource.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionMatchedPopulation N {r} initialPosition id
          hsource.toFinset 0 field)) () := by
    intro field
    simpa [RootIndexed.restartedRealPositionMatchedPopulation,
      RootIndexed.restartedRealPositionMatchedField,
      RootIndexed.selectedPopulationTotalized] using
      selectedReserveSpineRestartSourceOnLeft_initialInjection R growth hR hgrowth
        cap duration r N initialPosition field
  have hgeneric := RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N {r} initialPosition source hsource hinitial n
  filter_upwards [hgeneric] with field hgood
  have hcapacity' : ∀ k < n, (hsource.toFinset (k + 1) field).card ≤ N := by
    intro k hk
    have hcard := selectedReserveSpineRestartSourceOnLeft_card_le R growth hR hgrowth
      cap duration hbounded hcap r (k + 1) field
    omega
  simpa [source] using hgood hcapacity'

/-- At any fixed reserve-spine split, a successful cap-stopped growth trial
forces the rank-installed first-`N` population to contain at least the trial's
endpoint count, almost surely. This is the concrete success-event consequence
of the finite-window causal-source coupling. -/
theorem selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidate_success_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      selectedReserveSpineAlive R r k (RootIndexed.StepField.left field) →
      RootIndexed.StepField.left field r
          (selectedReserveSpinePath R r k (RootIndexed.StepField.left field)) ∈ splitBy R →
      growthTrialSuccess growth lower upper duration
        (fun v =>
          let q := (selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
            R r PUnit.unit (k + 1) (RootIndexed.StepField.left field)
          RootIndexed.StepField.left field q.1 (q.2 ++ v)) →
      lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
        initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset (k + 1 + duration) field).card := by
  have hcoupling := selectedReserveSpineRestartCoupledInjection_ae
    μ hnorm N initialPosition R growth hR hgrowth upper duration hbounded hupper
    hcapacity (r := r) (n := k + 1 + duration)
  filter_upwards [hcoupling] with field hdom
  intro halive hsplit hsuccess
  have hsourceCard := selectedReserveSpineRestartSource_card_ge_of_candidate_success
    R growth hR lower upper duration r k (RootIndexed.StepField.left field)
    halive hsplit hupper hsuccess
  rcases hdom with ⟨dom⟩
  have hcard := Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
    id id
    (RootIndexed.BranchingWalk.ofStepField initialPosition
      (RootIndexed.StepField.left field))
    (RootIndexed.BranchingWalk.ofStepField initialPosition
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset (k + 1 + duration) field))
    ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
      upper duration r).toFinset (k + 1 + duration) field)
    (RootIndexed.restartedRealPositionMatchedPopulation N {r} initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset (k + 1 + duration) field)
    dom
  have hsourceEq :
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset (k + 1 + duration) field =
      selectedReserveSpineRestartSourceSlice R growth hR upper duration r
        (k + 1 + duration) (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hcardSource :
      (selectedReserveSpineRestartSourceSlice R growth hR upper duration r
        (k + 1 + duration) (RootIndexed.StepField.left field)).card ≤
      (RootIndexed.restartedRealPositionMatchedPopulation N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset (k + 1 + duration) field).card := by
    calc
      _ = ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset (k + 1 + duration) field).card :=
        (congrArg Finset.card hsourceEq).symm
      _ ≤ _ := hcard
  exact hsourceCard.trans hcardSource

/-- On the first-success event already indexed on the full pre-sampled
reserve tree, the rank-installed population at that candidate endpoint has
at least the requested number of particles almost surely. -/
theorem selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidateSuccessEvent_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      RootIndexed.StepField.left field ∈
          selectedReserveSpineCandidateSuccessEvent R growth hR
            lower upper duration r k →
      lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
        initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset (k + 1 + duration) field).card := by
  have h := selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidate_success_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r k
  filter_upwards [h] with field hfield
  intro hsuccess
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_setOf_eq] at hsuccess
  rcases hsuccess with ⟨halive, hsplit, hgrowthSuccess⟩
  exact hfield halive hsplit hgrowthSuccess

/-- Every particle in the causal reserve source has a matched particle in the
rank-installed `N` population whose position is no larger.  This is the
position-sensitive comparison needed for right-tail bounds on the minimum;
the candidate-union population need not equal the retrospective restart. -/
theorem selectedReserveSpineRestartCoupled_position_witness_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (cap duration : ℕ) (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (hcapacity : 1 + (duration + 1) * (2 * cap) ≤ N)
    (r : Root) (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      ∀ q ∈ selectedReserveSpineRestartSourceSlice R growth hR cap duration r n
          (RootIndexed.StepField.left field),
        ∃ p ∈ RootIndexed.restartedRealPositionMatchedPopulation N {r}
            initialPosition id
            (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
              hgrowth cap duration r).toFinset n field,
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
              (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                hgrowth cap duration r).toFinset n field)).position id p.1 p.2 ≤
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field)).position id q.1 q.2 := by
  have hcoupling := selectedReserveSpineRestartCoupledInjection_ae
    μ hnorm N initialPosition R growth hR hgrowth cap duration hbounded hcap
    hcapacity r n
  filter_upwards [hcoupling] with field hdom
  intro q hq
  rcases hdom with ⟨dom⟩
  let hleft := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth cap duration r
  have hsourceEq : hleft.toFinset n field =
      selectedReserveSpineRestartSourceSlice R growth hR cap duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    simp [selectedReserveSpineRestartSourceOnLeft,
      RootIndexed.CausalPopulation.pullback_population,
      selectedReserveSpineRestartSource]
  have hqSource : q ∈ hleft.toFinset n field := by
    rw [hsourceEq]
    exact hq
  have hqCloud : q ∈
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hleft.toFinset n field)).particles () := by
    simpa [Combinatorics.Branching.Selection.Coupling.populationCloud] using hqSource
  refine ⟨dom q, ?_, ?_⟩
  · have hmem := dom.mapsTo hqCloud
    simpa [Combinatorics.Branching.Selection.Coupling.populationCloud] using hmem
  · have hpos := dom.dominates q hqCloud
    simpa [Combinatorics.Branching.Selection.Coupling.populationCloud] using hpos

/-- At each candidate endpoint, every particle of the cap-stopped trial has
a corresponding rank-installed `N` particle at a weakly smaller position.
This states the exact one-sided spatial comparison used by a right-tail
argument, conditional only on the observable reserve split. -/
theorem selectedReserveSpineRestartCoupledCandidate_position_witness_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (cap duration : ℕ) (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (hcapacity : 1 + (duration + 1) * (2 * cap) ≤ N)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      selectedReserveSpineAlive R r k (RootIndexed.StepField.left field) →
      RootIndexed.StepField.left field r
        (selectedReserveSpinePath R r k (RootIndexed.StepField.left field)) ∈ splitBy R →
      ∀ q ∈ rootedCapStoppedPopulation growth cap (RootIndexed.StepField.left field)
          ((selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
            R r PUnit.unit (k + 1) (RootIndexed.StepField.left field)) duration,
        ∃ p ∈ RootIndexed.restartedRealPositionMatchedPopulation N {r}
            initialPosition id
            (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
              hgrowth cap duration r).toFinset (k + 1 + duration) field,
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
              (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                hgrowth cap duration r).toFinset (k + 1 + duration) field)).position id
              p.1 p.2 ≤
          (RootIndexed.BranchingWalk.ofStepField initialPosition
            (RootIndexed.StepField.left field)).position id q.1 q.2 := by
  have hwitness := selectedReserveSpineRestartCoupled_position_witness_ae
    μ hnorm N initialPosition R growth hR hgrowth cap duration hbounded hcap
    hcapacity r (k + 1 + duration)
  filter_upwards [hwitness] with field hfield
  intro halive hsplit q hq
  have hsource := selectedReserveSpineCandidate_subset_restartSource_at_endpoint
    R growth hR cap duration r k (RootIndexed.StepField.left field) halive hsplit hq
  exact hfield q hsource

/-- At the random first successful candidate completion, the rank-installed
`N` population contains at least the candidate's lower population bound, and
every particle of that successful candidate has a matched particle at a weakly
smaller position. The candidate index and completion generation are returned
explicitly; this is an endpoint comparison, not yet a post-endpoint restart
law. -/
theorem selectedReserveSpineFirstSuccess_endpointComparison_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity :
      1 + (duration + 1) * (2 * upper) ≤ N)
    (r : Root) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
          lower upper duration r (RootIndexed.StepField.left field) ≠ ⊤ →
      ∃ k : ℕ, ∃ n : ℕ,
        selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
            lower upper duration r (RootIndexed.StepField.left field) =
              (n : WithTop ℕ) ∧
        ((k + 1 + duration : ℕ) : WithTop ℕ) = (n : WithTop ℕ) ∧
        RootIndexed.StepField.left field ∈
          selectedReserveSpineCandidateSuccessEvent R growth hR
            lower upper duration r k ∧
        lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
          initialPosition id
          (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
            upper duration r).toFinset n field).card ∧
        ∀ q ∈ rootedCapStoppedPopulation growth upper
            (RootIndexed.StepField.left field)
            ((selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
              R r PUnit.unit (k + 1) (RootIndexed.StepField.left field)) duration,
          ∃ p ∈ RootIndexed.restartedRealPositionMatchedPopulation N {r}
              initialPosition id
              (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                hgrowth upper duration r).toFinset n field,
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
                (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                  hgrowth upper duration r).toFinset n field)).position id p.1 p.2 ≤
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field)).position id q.1 q.2 := by
  have hcardAll : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      ∀ k, RootIndexed.StepField.left field ∈
          selectedReserveSpineCandidateSuccessEvent R growth hR
            lower upper duration r k →
        lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
          initialPosition id
          (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
            upper duration r).toFinset (k + 1 + duration) field).card := by
    apply ae_all_iff.2
    intro k
    exact selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidateSuccessEvent_ae
      μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
      hbounded hcapacity r k
  have hwitnessAll : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      ∀ k, RootIndexed.StepField.left field ∈
          selectedReserveSpineCandidateSuccessEvent R growth hR
            lower upper duration r k →
        ∀ q ∈ rootedCapStoppedPopulation growth upper
            (RootIndexed.StepField.left field)
            ((selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
              R r PUnit.unit (k + 1) (RootIndexed.StepField.left field)) duration,
          ∃ p ∈ RootIndexed.restartedRealPositionMatchedPopulation N {r}
              initialPosition id
              (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                hgrowth upper duration r).toFinset (k + 1 + duration) field,
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
                (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
                  hgrowth upper duration r).toFinset (k + 1 + duration) field)).position id
                p.1 p.2 ≤
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field)).position id q.1 q.2 := by
    apply ae_all_iff.2
    intro k
    have h := selectedReserveSpineRestartCoupledCandidate_position_witness_ae
      μ hnorm N initialPosition R growth hR hgrowth upper duration hbounded hupper
      hcapacity r k
    filter_upwards [h] with field hfield
    intro hsuccess
    simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_setOf_eq] at hsuccess
    rcases hsuccess with ⟨halive, hsplit, _⟩
    exact hfield halive hsplit
  filter_upwards [hcardAll, hwitnessAll] with field hcard hwitness
  intro hfinite
  let declarations : ℕ → Set (RootIndexed.StepField Root α ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k}
  have htime :
      selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
          lower upper duration r (RootIndexed.StepField.left field) ≠ ⊤ := hfinite
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htime
  have hntime :
      selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
        lower upper duration r (RootIndexed.StepField.left field) =
          (n : WithTop ℕ) := hn.symm
  have hfirst :
      firstDeclaredSuccess declarations (RootIndexed.StepField.left field) =
        (n : WithTop ℕ) := by
    simpa [selectedReserveSpineFirstSuccessfulCandidateCompletion, declarations]
      using hntime
  have hdecl := (firstDeclaredSuccess_eq_iff declarations
    (RootIndexed.StepField.left field) n).mp hfirst
  obtain ⟨k, hkn, hsuccess⟩ := hdecl.1
  have htimeNat : k + 1 + duration = n := WithTop.coe_injective hkn
  have hsuccess' : RootIndexed.StepField.left field ∈
      selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k := by
    simpa [declarations] using hsuccess
  have hcard' := hcard k hsuccess'
  have hcardN : lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field).card := by
    simpa [htimeNat] using hcard'
  have hsuccessMem := hsuccess'
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_setOf_eq] at hsuccessMem
  rcases hsuccessMem with ⟨halive, hsplit, hgrowthSuccess⟩
  have hwitness' := hwitness k ⟨halive, hsplit, hgrowthSuccess⟩
  have hwitnessN : ∀ q ∈ rootedCapStoppedPopulation growth upper
      (RootIndexed.StepField.left field)
      ((selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
        R r PUnit.unit (k + 1) (RootIndexed.StepField.left field)) duration,
      ∃ p ∈ RootIndexed.restartedRealPositionMatchedPopulation N {r}
          initialPosition id
          (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
            hgrowth upper duration r).toFinset n field,
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
            (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
              hgrowth upper duration r).toFinset n field)).position id p.1 p.2 ≤
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field)).position id q.1 q.2 := by
    intro q hq
    rcases hwitness' q hq with ⟨p, hp, hpos⟩
    exact ⟨p, by simpa [htimeNat] using hp,
      by simpa [htimeNat] using hpos⟩
  exact ⟨k, n, hfirst, hkn, hsuccess', hcardN, hwitnessN⟩

/-- The particle of prescribed dynamic rank at a random stopping generation.
At `⊤` this is totalized to `none`; at a finite time it is the ordinary
finite-stage rank selector. -/
noncomputable def particleAtRankByAtStoppingTime
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (rank : ℕ) : Ω → Option ι :=
  fun ω => match τ ω with
  | ⊤ => none
  | (n : ℕ) => particleAtRankBy (value n ω) (candidates n ω) rank

@[simp] theorem particleAtRankByAtStoppingTime_eq_finite
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (rank : ℕ)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ)) :
    particleAtRankByAtStoppingTime τ value candidates rank ω =
      particleAtRankBy (value n ω) (candidates n ω) rank := by
  simp [particleAtRankByAtStoppingTime, hτ]

/-- A finite vector of the first `m` dynamic ranks at a stopping generation.
The default value only totalizes the selector when the stopping time is
infinite or the requested rank is absent. -/
noncomputable def particleRankVectorAtStoppingTime
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι) :
    Ω → Fin m → ι :=
  fun ω i => (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default

theorem measurable_particleRankVectorAtStoppingTime
    {Ω ι Value : Type*} [MeasurableSpace Ω] [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [LinearOrder ι] [LinearOrder Value]
    (F : Filtration ℕ inferInstance) (τ : Ω → WithTop ℕ)
    (hτ : IsStoppingTime F τ)
    (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι)
    (hcandidateFiber : ∀ n s, MeasurableSet[F n]
      {ω | candidates n ω = s})
    (hcandidateRange : ∀ n, (Set.range (candidates n)).Countable)
    (hkey : ∀ n p q, Measurable[F n]
      (fun ω => valueKey (value n ω) q < valueKey (value n ω) p))
    (m : ℕ) (default : ι) :
    Measurable[hτ.measurableSpace]
      (particleRankVectorAtStoppingTime τ value candidates m default) := by
  classical
  have hcoord : ∀ i : Fin m, Measurable[hτ.measurableSpace]
      (fun ω => particleRankVectorAtStoppingTime τ value candidates m default ω i) := by
    intro i
    have htime (n : ℕ) : MeasurableSet[hτ.measurableSpace]
        {ω | τ ω = (n : WithTop ℕ)} := hτ.measurableSet_eq_of_countable' n
    have timeCell (n : ℕ) (E : Set Ω) (hE : MeasurableSet[F n] E) :
        MeasurableSet[hτ.measurableSpace]
          (E ∩ {ω | τ ω = (n : WithTop ℕ)}) :=
      (hτ.measurableSet_inter_eq_iff E n).2
        (hE.inter (hτ.measurableSet_eq n))
    have htop : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} :=
      hτ.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    have hsome (p : ι) (n : ℕ) : MeasurableSet[F n]
        {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p} := by
      letI : MeasurableSpace Ω := F n
      exact measurableSet_particleAtRankBy_eq_some (fun ω => value n ω)
        (fun ω => candidates n ω) (hcandidateFiber n) (hcandidateRange n)
        (hkey n) i.1 p
    have hnone (n : ℕ) : MeasurableSet[F n]
        {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = none} := by
      letI : MeasurableSpace Ω := F n
      exact measurableSet_particleAtRankBy_eq_none (fun ω => value n ω)
        (fun ω => candidates n ω) (hcandidateFiber n) (hcandidateRange n) i.1
    have hfiber (p : ι) : MeasurableSet[hτ.measurableSpace]
        {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} := by
      by_cases hp : p = default
      · have hdecomp :
            {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} =
              {ω | τ ω = ⊤} ∪ ⋃ n : ℕ,
                ({ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = none} ∪
                  {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p}) ∩
                    {ω | τ ω = (n : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion,
            Set.mem_inter_iff]
          cases ht : τ ω with
          | top => simp [particleAtRankByAtStoppingTime, ht, hp]
          | coe n =>
              rw [particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n ht]
              simp only [WithTop.coe_ne_top, false_or]
              cases hv : particleAtRankBy (value n ω) (candidates n ω) i.1 with
              | none =>
                  simp only [hv, Option.getD_none]
                  constructor
                  · intro _
                    exact ⟨n, Or.inl hv, rfl⟩
                  · intro _
                    simpa [hp]
              | some q =>
                  simp only [hv, Option.getD_some]
                  constructor
                  · intro hqp
                    exact ⟨n, Or.inr (by simp [hv, hqp]), rfl⟩
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    simpa [hv] using hk
        rw [hdecomp]
        refine htop.union (MeasurableSet.iUnion fun n => ?_)
        have hstage := (hnone n).union (hsome p n)
        exact timeCell n _ hstage
      · have hdecomp :
            {ω | (particleAtRankByAtStoppingTime τ value candidates i.1 ω).getD default = p} =
              ⋃ n : ℕ,
                {ω | particleAtRankBy (value n ω) (candidates n ω) i.1 = some p} ∩
                  {ω | τ ω = (n : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
          cases ht : τ ω with
          | top =>
              have hdefaultNe : default ≠ p := fun h => hp h.symm
              simp [particleAtRankByAtStoppingTime, ht, hdefaultNe]
          | coe n =>
              rw [particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n ht]
              cases hv : particleAtRankBy (value n ω) (candidates n ω) i.1 with
              | none =>
                  simp only [hv, Option.getD_none]
                  constructor
                  · intro hdefault
                    exact False.elim (hp (hdefault.symm))
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    exact False.elim (by simpa [hv] using hk)
              | some q =>
                  simp only [hv, Option.getD_some]
                  constructor
                  · intro hqp
                    exact ⟨n, by simpa [hv, hqp], rfl⟩
                  · rintro ⟨k, hk, htime⟩
                    have hkn : k = n := (WithTop.coe_injective htime).symm
                    subst k
                    simpa [hv] using hk
        rw [hdecomp]
        exact MeasurableSet.iUnion fun n => timeCell n _ (hsome p n)
    letI : MeasurableSpace Ω := hτ.measurableSpace
    change Measurable (fun ω => particleRankVectorAtStoppingTime
      τ value candidates m default ω i)
    apply measurable_to_countable'
    intro p
    have hset :
        (fun ω => particleRankVectorAtStoppingTime τ value candidates m default ω i) ⁻¹'
          {p} =
        {ω | particleRankVectorAtStoppingTime τ value candidates m default ω i = p} := by
      ext ω
      simp
    rw [hset]
    exact hfiber p
  letI : MeasurableSpace Ω := hτ.measurableSpace
  exact measurable_pi_iff.mpr hcoord

/-- The first-success completion time viewed on the common two-root field.
Candidate times and success events are pulled back from the left copy, so the
time remains adapted to the joint domain filtration. -/
noncomputable def selectedReserveSpineRestartEndpointTime
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    RootIndexed.StepField (Root ⊕ Root) α ℝ → WithTop ℕ :=
  fun field => selectedReserveSpineFirstSuccessfulCandidateCompletion
    R growth hR lower upper duration r (RootIndexed.StepField.left field)

theorem selectedReserveSpineRestartEndpointTime_isStoppingTime
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ))
      (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
        lower upper duration r) := by
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let G := RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)
  let τ := selectedReserveSpineFirstSuccessfulCandidateCompletion
    R growth hR lower upper duration r
  have hτ : IsStoppingTime G τ :=
    selectedReserveSpineFirstSuccessfulCandidateCompletion_isStoppingTime
      R growth hR hgrowth lower upper duration r
  intro n
  have hleft : @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (RootIndexed.StepField Root α ℝ) (F n) (G n)
      RootIndexed.StepField.left := by
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α ℝ →
          RootIndexed.StepField Root α ℝ) by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable Sum.inl n
  have hevent : {field | τ (RootIndexed.StepField.left field) ≤ n} =
      RootIndexed.StepField.left ⁻¹' {ω | τ ω ≤ n} := by
    ext field
    rfl
  change MeasurableSet[F n] {field | τ (RootIndexed.StepField.left field) ≤ n}
  rw [hevent]
  exact (hτ.measurableSet_le n).preimage hleft

/-- At the random first-success endpoint, enumerate the first `lower`
rank-installed target particles by their ordinary finite-generation spatial
rank. The vector is totalized if completion never occurs or the requested
rank is absent. -/
noncomputable def selectedReserveSpineRestartEndpointRankVector
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) : Fin lower →
      RootIndexed.TreeNode Root α := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSource R growth hR hgrowth
    upper duration r
  exact particleRankVectorAtStoppingTime
    (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset n field) p)
    (fun n field => RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id hsource.toFinset n field)
    lower (r, []) field

/-- The concrete target endpoint vector is measurable in the stopped domain
filtration. Its stagewise candidate population is the selected population on
the recursively rank-installed field; the preceding choices and their spatial
keys are measurable at the generations that reveal them. -/
theorem selectedReserveSpineRestartEndpointRankVector_measurable
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (selectedReserveSpineRestartEndpointRankVector N initialPosition R growth
        hR hgrowth lower upper duration r) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let sourceValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let targetValue := fun k (_ : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k field p
  let sourceSet := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) =>
    hsource.toFinset k field
  let target := fun k (_ : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ) =>
    RootIndexed.selectedPopulationTotalized N {r} initialPosition id id k field
  have hsourceDepth : ∀ k field p, p ∈ sourceSet k field → p.2.length = k := by
    intro k field p hp
    exact source.depth k field p ((hsource.mem_toFinset k field p).mp hp)
  have hsourceFiber : ∀ k s, MeasurableSet[F k]
      {field | sourceSet k field = s} := by
    intro k s
    exact (hsource.measurable_toFinset k) (measurableSet_singleton s)
  have hsourceRange : ∀ k, (Set.range (sourceSet k)).Countable :=
    fun _ => Set.to_countable _
  have hsourceKey : ∀ k p q, Measurable[F k]
      fun field => valueKey (sourceValue k field) q < valueKey (sourceValue k field) p := by
    intro k p q
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F k
    apply Selection.NSelection.measurable_valueKey_lt
    intro z
    exact (RootIndexed.positionAtGeneration_measurable initialPosition id
      measurable_id k z.1 z.2).comp
        (RootIndexed.StepField.reindex_filtration_measurable Sum.inl k)
  have hstage : ∀ n,
      (Set.range (RootIndexed.rankInstalledBlockChoice
        sourceValue targetValue sourceSet target n)).Countable ∧
      ∀ choices, MeasurableSet[F n]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          sourceSet target n field = choices} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hpriorCount : ∀ k, k < n → (Set.range
            (RootIndexed.rankInstalledBlockChoice sourceValue targetValue
              sourceSet target k)).Countable := fun k hk => (ih k hk).1
        have hpriorFiber : ∀ k, k < n → ∀ choices,
            MeasurableSet[RootIndexed.stepFiltration
              (Root := Root ⊕ Root) (α := α) (X := ℝ) k]
              {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
                sourceSet target k field = choices} :=
          fun k hk => (ih k hk).2
        have htargetMeas : Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            (fun field => target n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
          by
            simpa [target] using
              (RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
                N {r} initialPosition id measurable_id id measurable_id
                sourceValue targetValue sourceSet target hsourceDepth n
                hpriorCount hpriorFiber)
        have htargetFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            {field | target n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
          fun s => htargetMeas (measurableSet_singleton s)
        have htargetRange : (Set.range fun field => target n field
            (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
              RootIndexed.StepField.left RootIndexed.StepField.right n field)
            ).Countable := Set.to_countable _
        have htargetKey : ∀ p q, Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            fun field => valueKey (targetValue n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
              valueKey (targetValue n field
                (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                  RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
          let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
            RootIndexed.stepFiltration
              (Root := Root ⊕ Root) (α := α) (X := ℝ) n
          intro p q
          exact Selection.NSelection.measurable_valueKey_lt
            (fun field z => targetValue n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field) z)
            (fun z => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
              initialPosition id measurable_id id measurable_id sourceValue targetValue
              sourceSet target hsourceDepth n hpriorCount hpriorFiber z) p q
        constructor
        · exact RootIndexed.rankBlockChoice_range_countable_of_supports n
            (sourceValue n)
            (fun field => targetValue n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (sourceSet n)
            (fun field => target n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (hsourceRange n) htargetRange
        · intro choices
          exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
            (sourceValue n)
            (fun field => targetValue n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (sourceSet n)
            (fun field => target n field
              (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (hsourceFiber n) (hsourceRange n) htargetFiber htargetRange
            (hsourceKey n) htargetKey choices
  have htargetMeas (n : ℕ) : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
      (fun field => target n field
        (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
    by
      simpa [target] using
        (RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
          N {r} initialPosition id measurable_id id measurable_id sourceValue targetValue
          sourceSet target hsourceDepth n
          (fun k hk => (hstage k).1) (fun k hk => (hstage k).2))
  have htargetFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n]
        {field | target n field
          (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
            RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
    htargetMeas n (measurableSet_singleton s)
  have htargetRange (n : ℕ) : (Set.range fun field => target n field
      (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
      ).Countable := Set.to_countable _
  have htargetKey (n : ℕ) : ∀ p q, Measurable[F n]
      fun field => valueKey (targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (targetValue n field
          (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F n
    intro p q
    exact Selection.NSelection.measurable_valueKey_lt
      (fun field z => targetValue n field
        (RootIndexed.rankInstalledField sourceValue targetValue sourceSet target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) z)
      (fun z => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
        initialPosition id measurable_id id measurable_id sourceValue targetValue
        sourceSet target hsourceDepth n
        (fun k hk => (hstage k).1) (fun k hk => (hstage k).2) z) p q
  let candidates := fun n field =>
    RootIndexed.restartedRealPositionMatchedPopulation N {r} initialPosition id
      hsource.toFinset n field
  let value := fun n field p =>
    RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset n field) p
  have hcandidateFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n] {field | candidates n field = s} := by
    simpa [candidates, target, RootIndexed.restartedRealPositionMatchedPopulation,
      RootIndexed.restartedRealPositionMatchedField, sourceSet, sourceValue, targetValue]
      using htargetFiber n s
  have hcandidateRange (n : ℕ) : (Set.range (candidates n)).Countable :=
    Set.to_countable _
  have hkey (n : ℕ) (p q : RootIndexed.TreeNode Root α) : Measurable[F n]
      fun field => valueKey (value n field) q < valueKey (value n field) p := by
    simpa [value, targetValue, RootIndexed.restartedRealPositionMatchedField,
      sourceSet, sourceValue, targetValue] using htargetKey n p q
  have hτ : IsStoppingTime F τ := by
    simpa [τ, selectedReserveSpineRestartEndpointTime] using
      selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r
  have hmeas := measurable_particleRankVectorAtStoppingTime F τ hτ
    value candidates hcandidateFiber hcandidateRange hkey lower (r, [])
  change Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
    (particleRankVectorAtStoppingTime τ value candidates lower (r, []))
  exact hmeas

/-- Rank the causal source population itself at the first successful
completion time. This supplies a pointwise fallback for raw fields where the
rank-installed target happens to have too few particles; on every finite
successful completion the source has at least `lower` particles. -/
noncomputable def selectedReserveSpineRestartSourceEndpointRankVector
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) : Fin lower →
      RootIndexed.TreeNode Root α := by
  classical
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  exact particleRankVectorAtStoppingTime
    (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p)
    (fun n field => hsource.toFinset n field)
    lower (r, []) field

/-- The stopped source-rank vector is measurable in the first-success
completion filtration. -/
theorem selectedReserveSpineRestartSourceEndpointRankVector_measurable
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let value := fun n (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p
  let candidates := fun n field => hsource.toFinset n field
  have hτ : IsStoppingTime F τ := by
    simpa [τ, selectedReserveSpineRestartEndpointTime] using
      selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r
  have hdepth : ∀ n field p, p ∈ candidates n field → p.2.length = n := by
    intro n field p hp
    exact source.depth n field p ((hsource.mem_toFinset n field p).mp hp)
  have hfiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n] {field | candidates n field = s} := by
    exact hsource.measurable_toFinset n (measurableSet_singleton s)
  have hrange (n : ℕ) : (Set.range (candidates n)).Countable := Set.to_countable _
  have hkey (n : ℕ) (p q : RootIndexed.TreeNode Root α) : Measurable[F n]
      fun field => valueKey (value n field) q < valueKey (value n field) p := by
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F n
    exact Selection.NSelection.measurable_valueKey_lt
      (fun field z => value n field z)
      (fun z =>
        (RootIndexed.positionAtGeneration_measurable initialPosition id
          measurable_id n z.1 z.2).comp
          (RootIndexed.StepField.reindex_filtration_measurable Sum.inl n)) p q
  have hmeas := measurable_particleRankVectorAtStoppingTime F τ hτ value
    candidates hfiber hrange hkey lower (r, [])
  change Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
    (particleRankVectorAtStoppingTime τ value candidates lower (r, []))
  exact hmeas

/-- Endpoint roots for a fresh-field factorization. At a rank present in the
rank-installed target population, use the right-copy target particle. If a
raw exceptional field has too few target particles, use the matching rank
from the causal source on the left copy instead. The sum tag keeps the two
fallback populations disjoint. -/
noncomputable def selectedReserveSpineRestartEndpointFreshRoots
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
    Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
  fun i =>
    let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    if target = (r, []) then
      (Sum.inl r, (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).2)
    else
      (Sum.inr r, target.2)

/-- The mixed endpoint-root vector is measurable in the stopping-time
filtration. The branch test is measurable because the target rank vector is
measurable and its default node is a measurable singleton. -/
theorem selectedReserveSpineRestartEndpointFreshRoots_measurable
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := (selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r).measurableSpace
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let source := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  have htarget : Measurable[F] target := by
    simpa [F, target] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hsource : Measurable[F] source := by
    simpa [F, source] using
      selectedReserveSpineRestartSourceEndpointRankVector_measurable initialPosition
        R growth hR hgrowth lower upper duration r
  have hcoord : ∀ i : Fin lower,
      Measurable[F] (fun field =>
        selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i) := by
    intro i
    change Measurable[F] (fun field => roots field i)
    let t := fun field => target field i
    let s := fun field => source field i
    have ht : Measurable[F] t := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ target)
      exact (measurable_pi_apply i).comp htarget
    have hs : Measurable[F] s := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ source)
      exact (measurable_pi_apply i).comp hsource
    have hdefault : MeasurableSet[F] {field | t field = (r, [])} :=
      ht (measurableSet_singleton (r, []))
    have htag : Measurable[F] (fun field =>
        if t field = (r, []) then (Sum.inl r : Root ⊕ Root) else Sum.inr r) :=
      Measurable.ite hdefault measurable_const measurable_const
    have hnode : Measurable[F] (fun field =>
        if t field = (r, []) then (s field).2 else (t field).2) :=
      Measurable.ite hdefault (hnodePath.comp hs) (hnodePath.comp ht)
    have hpair := htag.prodMk hnode
    have hrootEq : (fun field => roots field i) = fun field =>
        (if target field i = (r, []) then Sum.inl r else Sum.inr r,
          if target field i = (r, []) then (source field i).2 else (target field i).2) := by
      funext field
      by_cases h : target field i = (r, []) <;>
        simp [roots, selectedReserveSpineRestartEndpointFreshRoots, target, source, h]
    rw [hrootEq]
    exact hpair
  letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F
  exact measurable_pi_iff.mpr hcoord

/-- At a finite stopping generation, every requested rank below the candidate
cardinality is realized in the candidate set. -/
theorem particleRankVectorAtStoppingTime_mem
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) (i : Fin m) :
    particleRankVectorAtStoppingTime τ value candidates m default ω i ∈
      candidates n ω := by
  classical
  have hi : i.1 < (candidates n ω).card := lt_of_lt_of_le i.2 hm
  have hsome : particleAtRankBy (value n ω) (candidates n ω) i.1 ≠ none := by
    intro hnone
    have hcard := (particleAtRankBy_eq_none_iff).mp hnone
    omega
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' := (particleAtRankBy_eq_some_iff).mp hp.symm
  simpa [particleRankVectorAtStoppingTime,
    particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n hτ,
    hp.symm] using hp'.1

/-- The stopped rank vector has the prescribed ranks; consequently its
coordinates are pairwise distinct whenever it is requested below the finite
candidate cardinality. -/
theorem particleRankVectorAtStoppingTime_rank
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) (i : Fin m) :
    rankBy (value n ω) (candidates n ω)
      (particleRankVectorAtStoppingTime τ value candidates m default ω i) = i.1 := by
  classical
  have hmem := particleRankVectorAtStoppingTime_mem τ value candidates m default
    ω n hτ hm i
  have hi : i.1 < (candidates n ω).card := lt_of_lt_of_le i.2 hm
  have hsome : particleAtRankBy (value n ω) (candidates n ω) i.1 ≠ none := by
    intro hnone
    have hcard := (particleAtRankBy_eq_none_iff).mp hnone
    omega
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' := (particleAtRankBy_eq_some_iff).mp hp.symm
  have hpvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime,
      particleAtRankByAtStoppingTime_eq_finite τ value candidates i.1 ω n hτ, hp.symm]
  rw [hpvec]
  exact hp'.2

/-- If a stopped rank selector is not its default sentinel, it is the genuine
particle at that rank, without a separate lower bound on the whole finite
population. -/
theorem particleRankVectorAtStoppingTime_rank_of_ne_default
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (i : Fin m)
    (hne : particleRankVectorAtStoppingTime τ value candidates m default ω i ≠ default) :
    rankBy (value n ω) (candidates n ω)
      (particleRankVectorAtStoppingTime τ value candidates m default ω i) = i.1 := by
  classical
  have hsome : particleAtRankByAtStoppingTime τ value candidates i.1 ω ≠ none := by
    intro hnone
    apply hne
    simp [particleRankVectorAtStoppingTime, hnone]
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' : particleAtRankBy (value n ω) (candidates n ω) i.1 = some p := by
    simpa [particleAtRankByAtStoppingTime, hτ] using hp.symm
  have hvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime, hp.symm]
  rw [hvec]
  exact (particleAtRankBy_eq_some_iff.mp hp').2

/-- A nondefault stopped rank is an actual member of the candidate population,
even when the requested rank is not known to exist uniformly on every raw
field. -/
theorem particleRankVectorAtStoppingTime_mem_of_ne_default
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (i : Fin m)
    (hne : particleRankVectorAtStoppingTime τ value candidates m default ω i ≠ default) :
    particleRankVectorAtStoppingTime τ value candidates m default ω i ∈ candidates n ω := by
  classical
  have hsome : particleAtRankByAtStoppingTime τ value candidates i.1 ω ≠ none := by
    intro hnone
    apply hne
    simp [particleRankVectorAtStoppingTime, hnone]
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
  have hp' : particleAtRankBy (value n ω) (candidates n ω) i.1 = some p := by
    simpa [particleAtRankByAtStoppingTime, hτ] using hp.symm
  have hvec : particleRankVectorAtStoppingTime τ value candidates m default ω i = p := by
    simp [particleRankVectorAtStoppingTime, hp.symm]
  rw [hvec]
  exact (particleAtRankBy_eq_some_iff.mp hp').1

/-- Distinctness of the enumerated stopped population follows from the
injectivity of dynamic rank on a finite candidate set. -/
theorem particleRankVectorAtStoppingTime_injective
    {Ω ι Value : Type*} [LinearOrder ι] [LinearOrder Value]
    (τ : Ω → WithTop ℕ) (value : ℕ → Ω → ι → Value)
    (candidates : ℕ → Ω → Finset ι) (m : ℕ) (default : ι)
    (ω : Ω) (n : ℕ) (hτ : τ ω = (n : WithTop ℕ))
    (hm : m ≤ (candidates n ω).card) :
    Function.Injective (particleRankVectorAtStoppingTime τ value candidates m default ω) := by
  intro i j hij
  apply Fin.ext
  have hi := particleRankVectorAtStoppingTime_rank τ value candidates m default ω n hτ hm i
  have hj := particleRankVectorAtStoppingTime_rank τ value candidates m default ω n hτ hm j
  rw [hij] at hi
  omega

/-- A finite endpoint time is exactly the end of one successful fixed-index
trial. -/
theorem selectedReserveSpineRestartEndpoint_success_of_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    ∃ k : ℕ, k + 1 + duration = n ∧
      RootIndexed.StepField.left field ∈
        selectedReserveSpineCandidateSuccessEvent R growth hR
          lower upper duration r k := by
  let declarations : ℕ → Set (RootIndexed.StepField Root α ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k}
  have hfirst : firstDeclaredSuccess declarations (RootIndexed.StepField.left field) =
      (n : WithTop ℕ) := by
    simpa [selectedReserveSpineRestartEndpointTime,
      selectedReserveSpineFirstSuccessfulCandidateCompletion, declarations] using htime
  have hdecl := (firstDeclaredSuccess_eq_iff declarations
    (RootIndexed.StepField.left field) n).mp hfirst
  obtain ⟨k, hkn, hsuccess⟩ := hdecl.1
  refine ⟨k, ?_, ?_⟩
  · exact WithTop.coe_injective hkn
  · simpa [declarations] using hsuccess

/-- At any finite first-success endpoint, the all-candidate causal source
contains the requested number of particles, pathwise. -/
theorem selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    lower ≤ ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
      hgrowth upper duration r).toFinset n field).card := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  obtain ⟨k, hkn, hsuccess⟩ := selectedReserveSpineRestartEndpoint_success_of_finite
    R growth hR hgrowth lower upper duration r field n htime
  have hsuccess' := hsuccess
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_setOf_eq] at hsuccess'
  rcases hsuccess' with ⟨halive, hsplit, hgrowthSuccess⟩
  have hcard := selectedReserveSpineRestartSource_card_ge_of_candidate_success
    R growth hR lower upper duration r k (RootIndexed.StepField.left field)
    halive hsplit hupper (by simpa using hgrowthSuccess)
  have hsourceEq : (selectedReserveSpineRestartSourceOnLeft_finiteSlices
      R growth hR hgrowth upper duration r).toFinset n field =
      selectedReserveSpineRestartSourceSlice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  rw [hsourceEq]
  simpa [hkn] using hcard

/-- Every particle in the candidate-union source belongs to the fixed initial
root `r`. This is useful when converting rooted particles to subtree
addresses for the stopped branching factorization theorem. -/
theorem selectedReserveSpineRestartSourceSlice_root
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (upper duration : ℕ) (r : Root) (n : ℕ)
    (field : RootIndexed.StepField Root α ℝ)
    (q : RootIndexed.TreeNode Root α)
    (hq : q ∈ selectedReserveSpineRestartSourceSlice R growth hR upper duration r n field) :
    q.1 = r := by
  classical
  have hcapRoot {root q : RootIndexed.TreeNode Root α} {age : ℕ}
      (hq : q ∈ rootedCapStoppedPopulation growth upper field root age) :
      q.1 = root.1 := by
    rw [rootedCapStoppedPopulation, Finset.mem_map] at hq
    obtain ⟨u, _, hqeq⟩ := hq
    exact (congrArg Prod.fst hqeq).symm
  rw [selectedReserveSpineRestartSourceSlice, Finset.mem_union] at hq
  rcases hq with hspine | hcandidate
  · by_cases halive : selectedReserveSpineAlive R r n field
    · have hnode : q = (r, selectedReserveSpinePath R r n field) := by
        simpa [halive] using hspine
      simp [hnode]
    · simp [halive] at hspine
  · obtain ⟨k, hk, hq⟩ :=
      (mem_selectedReserveSpineCandidatePopulation_iff R growth hR upper duration r n field q).mp
        hcandidate
    let root := (selectedReserveSpineLineages R hR).firstChildRootAt R r
      PUnit.unit (k + 1) field
    have hroot : root.1 = r := by
      exact (selectedReserveSpineLineages R hR).firstChildRootAt_root
        R r PUnit.unit (k + 1) field
    exact (hcapRoot hq).trans hroot

/-- The mixed endpoint-root vector has the right absolute generation on every
finite successful path. Target roots are used when available; source roots
fill any missing target ranks on exceptional raw fields. -/
theorem selectedReserveSpineRestartEndpointFreshRoots_depth
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) (i : Fin lower) :
    (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i).2.length = n := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let sourceValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let sourceSet := fun k field => hsource.toFinset k field
  have hsourceCard := selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hsourceMem :
      selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i ∈ sourceSet n field := by
    change particleRankVectorAtStoppingTime τ sourceValue sourceSet lower (r, [])
      field i ∈ sourceSet n field
    exact particleRankVectorAtStoppingTime_mem τ sourceValue sourceSet lower (r, [])
      field n htime hsourceCard i
  have hsourceDepth :
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).2.length = n := by
    exact source.depth n field _
      ((hsource.mem_toFinset n field _).mp (by simpa [sourceSet] using hsourceMem))
  let targetValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset k field) p
  let targetSet := fun k field => RootIndexed.restartedRealPositionMatchedPopulation
    N {r} initialPosition id
    hsource.toFinset k field
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field i
  by_cases hdefault : target = (r, [])
  · have hnode :
        (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 =
          (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
            R growth hR hgrowth lower upper duration r field i).2 := by
      simp [selectedReserveSpineRestartEndpointFreshRoots, target, hdefault]
    rw [hnode]
    exact hsourceDepth
  · have hsome : particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field ≠ none := by
      intro hnone
      apply hdefault
      change (particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field).getD
          (r, []) = (r, [])
      simp [hnone]
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
    have hp' : particleAtRankBy (targetValue n field) (targetSet n field) i.1 = some p := by
      have hstop : particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field = some p := hp.symm
      rw [particleAtRankByAtStoppingTime_eq_finite τ targetValue targetSet i.1 field n
        (by simpa [τ] using htime)] at hstop
      exact hstop
    have htargetEq : target = p := by
      change (particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field).getD
        (r, []) = p
      rw [hp.symm]
      rfl
    have htargetStage : particleAtRankBy (targetValue n field)
        (targetSet n field) i.1 = some p := hp'
    have hmemTarget : p ∈ targetSet n field :=
      (particleAtRankBy_eq_some_iff.mp htargetStage).1
    have hdepthTarget := RootIndexed.selectedPopulationTotalized_depth
      N {r} initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p
      (by simpa [targetSet, RootIndexed.restartedRealPositionMatchedPopulation]
        using hmemTarget)
    have hdepthTarget' : p.2.length = n := hdepthTarget
    have hnode :
        (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 = target.2 := by
      simp [selectedReserveSpineRestartEndpointFreshRoots, target, hdefault]
    rw [hnode, htargetEq]
    exact hdepthTarget'

/-- At a finite successful endpoint, the mixed root vector is injective.
Ranks on either side are distinct, and the left/right root tags separate the
fallback source particles from target particles. -/
theorem selectedReserveSpineRestartEndpointFreshRoots_injective
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    Function.Injective (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let sourceValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let sourceSet := fun k field => hsource.toFinset k field
  let targetValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset k field) p
  let targetSet := fun k field => RootIndexed.restartedRealPositionMatchedPopulation
    N {r} initialPosition id
    hsource.toFinset k field
  have hsourceCard := selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hroot (i : Fin lower) :
      selectedReserveSpineRestartEndpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r field i =
        if selectedReserveSpineRestartEndpointRankVector N initialPosition
            R growth hR hgrowth lower upper duration r field i = (r, []) then
          (Sum.inl r, (selectedReserveSpineRestartSourceEndpointRankVector
            initialPosition R growth hR hgrowth lower upper duration r field i).2)
        else (Sum.inr r, (selectedReserveSpineRestartEndpointRankVector N initialPosition
          R growth hR hgrowth lower upper duration r field i).2) := by
    simp [selectedReserveSpineRestartEndpointFreshRoots]
  have hsourceSliceEq : sourceSet n field =
      selectedReserveSpineRestartSourceSlice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hsourceRoot (i : Fin lower) :
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    apply selectedReserveSpineRestartSourceSlice_root R growth hR upper duration r n
      (RootIndexed.StepField.left field)
    rw [← hsourceSliceEq]
    change particleRankVectorAtStoppingTime τ sourceValue sourceSet lower (r, [])
      field i ∈ sourceSet n field
    exact particleRankVectorAtStoppingTime_mem τ sourceValue sourceSet lower (r, [])
      field n htime hsourceCard i
  have htargetRoot (i : Fin lower)
      (hne : selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i ≠ (r, [])) :
      (selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    let t := selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    have hmem : t ∈ targetSet n field := by
      change particleRankVectorAtStoppingTime τ targetValue targetSet lower (r, [])
        field i ∈ targetSet n field
      have hne' := hne
      change particleRankVectorAtStoppingTime τ targetValue targetSet lower
        (r, []) field i ≠ (r, []) at hne'
      exact particleRankVectorAtStoppingTime_mem_of_ne_default τ targetValue targetSet
        lower (r, []) field n htime i hne'
    have hroot := RootIndexed.selectedPopulationTotalized_root_mem N {r}
      initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset n field) t
      (by simpa [targetSet, RootIndexed.restartedRealPositionMatchedPopulation] using hmem)
    simpa [t] using hroot
  intro i j hij
  let ti := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field i
  let tj := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field j
  let si := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r field i
  let sj := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r field j
  have hi : ti = (r, []) ∨ ti ≠ (r, []) := eq_or_ne ti (r, [])
  have hj : tj = (r, []) ∨ tj ≠ (r, []) := eq_or_ne tj (r, [])
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hpath : si.2 = sj.2 := by
      have h := hij
      rw [hroot i, hroot j] at h
      simpa [ti, tj, si, sj, hi, hj] using congrArg Prod.snd h
    have hnodes : si = sj := Prod.ext (hsourceRoot i |>.trans (hsourceRoot j).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank τ sourceValue sourceSet
      lower (r, []) field n htime hsourceCard i
    have hrj := particleRankVectorAtStoppingTime_rank τ sourceValue sourceSet
      lower (r, []) field n htime hsourceCard j
    change rankBy (sourceValue n field) (sourceSet n field) si = i.1 at hri
    change rankBy (sourceValue n field) (sourceSet n field) sj = j.1 at hrj
    rw [hnodes] at hri
    apply Fin.ext
    omega
  · rw [hroot i, hroot j] at hij
    simp [ti, tj, si, sj, hi, hj] at hij
  ·
    rw [hroot i, hroot j] at hij
    simp [ti, tj, si, sj, hi, hj] at hij
  · have hnodes : ti = tj := by
      have h := hij
      rw [hroot i, hroot j] at h
      have hpath : ti.2 = tj.2 := by
        simpa [ti, tj, si, sj, hi, hj] using congrArg Prod.snd h
      exact Prod.ext (htargetRoot i hi |>.trans (htargetRoot j hj).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank_of_ne_default τ targetValue
      targetSet lower (r, []) field n htime i hi
    have hrj := particleRankVectorAtStoppingTime_rank_of_ne_default τ targetValue
      targetSet lower (r, []) field n htime j hj
    change rankBy (targetValue n field) (targetSet n field) ti = i.1 at hri
    change rankBy (targetValue n field) (targetSet n field) tj = j.1 at hrj
    rw [hnodes] at hri
    apply Fin.ext
    omega

/-- Whenever the rank-installed target has at least `lower` particles at the
finite endpoint, the mixed root vector is entirely on the target/right side.
The almost-sure coupling supplies this cardinality premise on first success. -/
theorem selectedReserveSpineRestartEndpointFreshRoots_eq_target_of_card
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ))
    (hcard : lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field).card) (i : Fin lower) :
    selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i =
      (Sum.inr r, (selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).2) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  have hmem := particleRankVectorAtStoppingTime_mem
    (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p)
    (fun n field => RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    lower (r, []) field n htime hcard i
  have hdepth := RootIndexed.selectedPopulationTotalized_depth N {r}
    initialPosition id id n
    (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    (selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i)
    (by simpa [RootIndexed.restartedRealPositionMatchedPopulation,
      selectedReserveSpineRestartEndpointRankVector,
      particleRankVectorAtStoppingTime] using hmem)
  have hne : selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i ≠ (r, []) := by
    intro hEq
    have hnpos : 0 < n := by
      obtain ⟨k, hkn, _⟩ := selectedReserveSpineRestartEndpoint_success_of_finite
        R growth hR hgrowth lower upper duration r field n htime
      omega
    rw [hEq] at hdepth
    simp at hdepth
    omega
  simp [selectedReserveSpineRestartEndpointFreshRoots, hne]

/-- Almost surely, on a finite first-success endpoint, the mixed root vector
used for fresh-field factorization is exactly the endpoint vector selected
from the rank-installed target population. The source-tagged branch only
totalizes exceptional raw fields where the target rank is absent. -/
theorem selectedReserveSpineRestartEndpointFreshRoots_eq_target_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      selectedReserveSpineRestartEndpointTime R growth hR hgrowth
        lower upper duration r field ≠ ⊤ →
      ∀ i : Fin lower,
        selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i =
        (Sum.inr r,
          (selectedReserveSpineRestartEndpointRankVector N initialPosition
            R growth hR hgrowth lower upper duration r field i).2) := by
  have hcomparison := selectedReserveSpineFirstSuccess_endpointComparison_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r
  filter_upwards [hcomparison] with field hfield
  intro hfinite i
  have hleft : selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
      lower upper duration r (RootIndexed.StepField.left field) ≠ ⊤ := by
    simpa [selectedReserveSpineRestartEndpointTime] using hfinite
  obtain ⟨_, n, htime, _, _, hcard, _⟩ := hfield hleft
  have htime' : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ) := by
    simpa [selectedReserveSpineRestartEndpointTime] using htime
  exact selectedReserveSpineRestartEndpointFreshRoots_eq_target_of_card
    N initialPosition R growth hR hgrowth lower upper duration hupper r field n
    htime' hcard i

/-- Fresh descendant fields below the mixed endpoint roots factor from the
domain filtration on every finite first-success event. The root family is
pre-sampled and stopped-measurable; source-side fallback makes depth and
distinctness pointwise even on exceptional raw fields. -/
theorem selectedReserveSpineRestartEndpointFreshField_factorization_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (A : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (B : Set (Fin lower → Combinatorics.UlamHarris.TreeNode α → Step α ℝ))
    (hA : MeasurableSet[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector
            (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
              R growth hR hgrowth lower upper duration r) ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤}) *
      RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  let encode := fun field : RootIndexed.StepField (Root ⊕ Root) α ℝ =>
    fun i : Fin lower =>
      match (roots field i).1 with
      | Sum.inl _ => (false, (roots field i).2)
      | Sum.inr _ => (true, (roots field i).2)
  let decode := fun code : Fin lower → Bool × Combinatorics.UlamHarris.TreeNode α =>
    fun i => if (code i).1 then (Sum.inr r, (code i).2) else (Sum.inl r, (code i).2)
  have hdecode (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      roots field = decode (encode field) := by
    funext i
    let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    by_cases htarget : target = (r, [])
    · simp [roots, decode, encode, target, htarget,
        selectedReserveSpineRestartEndpointFreshRoots]
    · simp [roots, decode, encode, target, htarget,
        selectedReserveSpineRestartEndpointFreshRoots]
  have hcount : (Set.range roots).Countable := by
    have hdecodeCountable : (Set.range decode).Countable := Set.countable_range decode
    apply hdecodeCountable.mono
    rintro q ⟨field, rfl⟩
    exact ⟨encode field, (hdecode field).symm⟩
  have hroots : Measurable[hτ.measurableSpace] roots := by
    simpa [roots, hτ] using
      selectedReserveSpineRestartEndpointFreshRoots_measurable hnodePath
        N initialPosition
        R growth hR hgrowth lower upper duration r
  have hfiber (q : Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α) :
      MeasurableSet[hτ.measurableSpace] {field | roots field = q} := by
    have heq : {field | roots field = q} = ⋂ i, {field | roots field i = q i} := by
      ext field
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro h i
        exact congrFun h i
      · intro h
        funext i
        exact h i
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hcoord : Measurable[hτ.measurableSpace] (fun field => roots field i) :=
      (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α ℝ) (Fin lower)
        (fun _ => (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α)
        hτ.measurableSpace (fun _ => inferInstance) roots).mp hroots i
    have hsumSingleton : ∀ z : Root ⊕ Root,
        MeasurableSet ({z} : Set (Root ⊕ Root)) := by
      intro z
      cases z with
      | inl x =>
          rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
            Sum.inl '' ({x} : Set Root) by ext y; simp]
          exact (measurableSet_singleton x).inl_image
      | inr x =>
          rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
            Sum.inr '' ({x} : Set Root) by ext y; simp]
          exact (measurableSet_singleton x).inr_image
    have htag : MeasurableSet[hτ.measurableSpace]
        {field | (roots field i).1 = (q i).1} :=
      (measurable_fst.comp hcoord) (hsumSingleton (q i).1)
    have hnode : MeasurableSet[hτ.measurableSpace]
        {field | (roots field i).2 = (q i).2} :=
      (measurable_snd.comp hcoord) (measurableSet_singleton (q i).2)
    have hpair : {field | roots field i = q i} =
        {field | (roots field i).1 = (q i).1} ∩
          {field | (roots field i).2 = (q i).2} := by
      ext field
      simp [Prod.ext_iff]
    rw [hpair]
    exact htag.inter hnode
  have hdepth (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
      (htime : τ field = (n : WithTop ℕ)) (i : Fin lower) :
      (roots field i).2.length = n := by
    exact selectedReserveSpineRestartEndpointFreshRoots_depth N initialPosition
      R growth hR hgrowth lower upper duration hupper r field n htime i
  have hinj (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (hfinite : τ field ≠ ⊤) : Function.Injective (roots field) := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
    exact selectedReserveSpineRestartEndpointFreshRoots_injective N initialPosition
      R growth hR hgrowth lower upper duration hupper r field n hn.symm
  simpa [τ, hτ, roots] using
    RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots hcount hfiber hdepth hinj A B hA hB

/-- On a finite first-success event, the actual rank-installed endpoint roots
have fresh descendant fields with product law, independently of the stopped
domain past. This is the mixed-root factorization for populations started from
multiple roots: the totalized source fallback is removed using the a.e. endpoint
population comparison. -/
theorem selectedReserveSpineRestartEndpointTargetFreshField_factorization_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (A : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (B : Set (Fin lower → Combinatorics.UlamHarris.TreeNode α → Step α ℝ))
    (hA : MeasurableSet[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector
            (fun field i => (Sum.inr r,
              (selectedReserveSpineRestartEndpointRankVector N initialPosition
                R growth hR hgrowth lower upper duration r field i).2)) ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | selectedReserveSpineRestartEndpointTime R growth hR hgrowth
          lower upper duration r field ≠ ⊤}) *
      RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  let targetRoots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    ((Sum.inr r : Root ⊕ Root),
      (selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).2)
  have hroot := selectedReserveSpineRestartEndpointFreshRoots_eq_target_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r
  have hset :
      (A ∩ {field | τ field ≠ ⊤} ∩
        RootIndexed.selectedSubtreeStepFieldVector targetRoots ⁻¹' B) =ᵐ[
        RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ]
      (A ∩ {field | τ field ≠ ⊤} ∩
        RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) := by
    filter_upwards [hroot] with field hroot
    by_cases hfinite : τ field ≠ ⊤
    · have hroots : roots field = targetRoots field := by
        funext i
        exact hroot hfinite i
      have hvec : RootIndexed.selectedSubtreeStepFieldVector targetRoots field =
          RootIndexed.selectedSubtreeStepFieldVector roots field := by
        change RootIndexed.subtreeStepFieldVector (targetRoots field) field =
          RootIndexed.subtreeStepFieldVector (roots field) field
        exact congrArg (fun v => RootIndexed.subtreeStepFieldVector v field) hroots.symm
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      apply propext
      constructor
      · rintro ⟨⟨hAfield, hfinite'⟩, hBfield⟩
        exact ⟨⟨hAfield, hfinite'⟩, by rw [hvec] at hBfield; exact hBfield⟩
      · rintro ⟨⟨hAfield, hfinite'⟩, hBfield⟩
        exact ⟨⟨hAfield, hfinite'⟩, by rw [← hvec] at hBfield; exact hBfield⟩
    · simp [hfinite]
  calc
    _ = RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
        (A ∩ {field | τ field ≠ ⊤} ∩
          RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' B) := measure_congr hset
    _ = RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
          (A ∩ {field | τ field ≠ ⊤}) *
          RootIndexed.stepFieldLaw (Root := Fin lower) μ B := by
      exact selectedReserveSpineRestartEndpointFreshField_factorization_on_finite
        hnodePath μ N initialPosition R growth hR hgrowth lower upper duration
        hupper r A B hA hB

/-- Measurability of a field obtained by rebasing at a measurable,
countable-range family of roots. This is the stopped-time counterpart of
`RootIndexed.selectedSubtreeStepFieldVector_measurable`, whose roots all have
one fixed generation. -/
private theorem measurable_subtreeStepFieldVector_of_measurable_roots
    {Root κ α X : Type*} [MeasurableSpace X]
    [MeasurableSpace κ] [MeasurableSpace Root]
    [MeasurableSpace (Combinatorics.UlamHarris.RootIndexed.TreeNode Root α)]
    [Countable κ] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass
      (Combinatorics.UlamHarris.RootIndexed.TreeNode Root α)]
    (roots : RootIndexed.StepField Root α X →
      κ → Combinatorics.UlamHarris.RootIndexed.TreeNode Root α)
    (hroots : Measurable roots)
    (hcount : (Set.range roots).Countable) :
    Measurable (fun ω => RootIndexed.subtreeStepFieldVector (roots ω) ω) := by
  classical
  let S : Set (κ → Combinatorics.UlamHarris.RootIndexed.TreeNode Root α) :=
    Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro B hB
  have hpre :
      (fun ω => RootIndexed.subtreeStepFieldVector (roots ω) ω) ⁻¹' B =
        ⋃ q : S, {ω | roots ω = q.1} ∩
          RootIndexed.subtreeStepFieldVector q.1 ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨roots ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨q, hq, h⟩
      simpa [hq] using h
  rw [hpre]
  exact MeasurableSet.iUnion fun q =>
    (hroots (measurableSet_singleton q.1)).inter
      ((RootIndexed.subtreeStepFieldVector_measurable q.1) hB)

/-- Joint law of the actual rank-installed endpoint positions and their
fresh target descendant field, restricted to finite first-success endpoints.
The position vector is measurable in the stopped domain filtration. The
fresh field has the independent `Fin lower` product law. Consequently this
identity can be pushed through any measurable *fixed finite-horizon*
observable of the retained positions and fresh field. It makes no assertion
about a random remaining horizon. -/
theorem selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (hpositions : Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace] positions) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let futureLaw := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
        (fun field => (positions field,
          RootIndexed.selectedSubtreeStepFieldVector
            (fun field i => (Sum.inr r,
              (selectedReserveSpineRestartEndpointRankVector N initialPosition
                R growth hR hgrowth lower upper duration r field i).2)) field)) =
      ((P.restrict {field | τ field ≠ ⊤}).map positions).prod futureLaw := by
  classical
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) := {field | τ field ≠ ⊤}
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let roots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (target field i).2)
  let fresh := fun field => RootIndexed.selectedSubtreeStepFieldVector roots field
  have hsumSingleton : ∀ z : Root ⊕ Root,
      MeasurableSet ({z} : Set (Root ⊕ Root)) := by
    intro z
    cases z with
    | inl x =>
        rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
          Sum.inl '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inl_image
    | inr x =>
        rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
          Sum.inr '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inr_image
  letI : MeasurableSingletonClass (Root ⊕ Root) := ⟨hsumSingleton⟩
  have hτmeas : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ := by
    simpa [τ] using hτ
  have htarget : Measurable[hτmeas.measurableSpace] target := by
    simpa [target, hτmeas] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hrootsStop : Measurable[hτmeas.measurableSpace] roots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace] (fun field => target field i) :=
      (measurable_pi_apply i).comp htarget
    have hpath := hnodePath.comp hi
    exact measurable_const.prodMk hpath
  have hrootsFull : Measurable roots := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hrootsStop.mono hle le_rfl
  have hcount : (Set.range roots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range roots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨target field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field => RootIndexed.subtreeStepFieldVector
      (roots field) field)
    exact measurable_subtreeStepFieldVector_of_measurable_roots roots hrootsFull hcount
  have hpositionsFull : Measurable positions := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hpositions.mono hle le_rfl
  have hpair : Measurable (fun field => (positions field, fresh field)) :=
    hpositionsFull.prodMk hfresh
  have hE : MeasurableSet E := by
    have htop : MeasurableSet[hτmeas.measurableSpace] {field | τ field = ⊤} :=
      hτmeas.measurable (measurableSet_singleton (⊤ : WithTop ℕ))
    have htopFull : MeasurableSet[⨆ n : ℕ,
        RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
        {field | τ field = ⊤}ᶜ := htop.compl.1
    have hle : (⨆ n : ℕ,
        RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ) n) ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le' n
    exact hle E htopFull
  have hleftFinite : IsFiniteMeasure ((P.restrict E).map
      (fun field => (positions field, fresh field))) := by infer_instance
  have hrect : ∀ {S : Set (Fin lower → ℝ)} {T : Set (Fin lower →
      Combinatorics.UlamHarris.TreeNode α → Step α ℝ)},
      MeasurableSet S → MeasurableSet T →
      ((P.restrict E).map (fun field => (positions field, fresh field)))
          (S ×ˢ T) =
        (((P.restrict E).map positions).prod Q) (S ×ˢ T) := by
    intro S T hS hT
    rw [Measure.map_apply hpair (hS.prod hT)]
    have hA : MeasurableSet[hτmeas.measurableSpace] (positions ⁻¹' S) :=
      hpositions hS
    have hfactor := selectedReserveSpineRestartEndpointTargetFreshField_factorization_on_finite
      hnodePath μ hnorm N initialPosition R growth hR hgrowth lower upper duration
      hupper hbounded hcapacity r (positions ⁻¹' S) T hA hT
    rw [show (positions ⁻¹' S ∩ E) ∩ fresh ⁻¹' T =
        E ∩ positions ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp [and_assoc, and_left_comm, and_comm]] at hfactor
    rw [Measure.restrict_apply (hpair (hS.prod hT))]
    rw [show (fun field => (positions field, fresh field)) ⁻¹' (S ×ˢ T) =
        positions ⁻¹' S ∩ fresh ⁻¹' T by
      ext field
      simp]
    rw [Measure.prod_prod, Measure.map_apply hpositionsFull hS,
      Measure.restrict_apply (hpositionsFull hS)]
    simpa [P, Q, E, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hfactor
  have hjoint :
      (P.restrict E).map (fun field => (positions field, fresh field)) =
        ((P.restrict E).map positions).prod Q :=
    Measure.ext_prod hrect
  simpa [τ, P, Q, E, fresh, roots] using hjoint

/-- Any measurable fixed-horizon observable of the stopped endpoint positions
and their fresh descendants has the product-law distribution obtained by
starting from the actual endpoint positions. This is deliberately a fixed
horizon pushforward theorem; it does not identify the law at a random
remaining time. -/
theorem selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite
    {Root α Outcome : Type*} {lower : ℕ} [Countable α] [MeasurableSpace α]
    [MeasurableSpace Outcome]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (fresh : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField (Fin lower) α ℝ)
    (hpair : Measurable (fun field => (positions field, fresh field)))
    (future : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ → Outcome)
    (hfreshLaw : ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
      (fun field => (positions field, fresh field)) =
        (((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
          (RootIndexed.stepFieldLaw (Root := Fin lower) μ))
    (hfuture : Measurable future) :
    ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
        (fun field => future (positions field, fresh field)) =
      ((((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
        (RootIndexed.stepFieldLaw (Root := Fin lower) μ)).map future := by
  rw [show (fun field => future (positions field, fresh field)) =
      future ∘ (fun field => (positions field, fresh field)) by rfl,
    ← Measure.map_map hfuture hpair, hfreshLaw]

private theorem observedPosition_jointInitial_measurable
    {lower : ℕ} {α : Type*} [MeasurableSpace α]
    (n : ℕ) (p : RootIndexed.TreeNode (Fin lower) α) :
    Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.observedPositionAtGeneration (fun i => z.1 i) id id n z.2 p) := by
  classical
  by_cases hp : p.2.length = n
  · have hinitial : Measurable (fun z : (Fin lower → ℝ) ×
        RootIndexed.StepField (Fin lower) α ℝ => z.1 p.1) :=
      (measurable_pi_apply p.1).comp measurable_fst
    have hdispField : Measurable[RootIndexed.stepFiltration
        (Root := Fin lower) (α := α) (X := ℝ) n]
        (fun field : RootIndexed.StepField (Fin lower) α ℝ =>
          Combinatorics.Branching.displaceWith id (field p.1) [] p.2) :=
      RootIndexed.displace_measurable id measurable_id p.1 [] p.2 n (by simpa [hp])
    have hdisp : Measurable (fun z : (Fin lower → ℝ) ×
        RootIndexed.StepField (Fin lower) α ℝ =>
          Combinatorics.Branching.displaceWith id (z.2 p.1) [] p.2) := by
      have hle : RootIndexed.stepFiltration
          (Root := Fin lower) (α := α) (X := ℝ) n ≤
          (inferInstance : MeasurableSpace
            (RootIndexed.StepField (Fin lower) α ℝ)) :=
        (RootIndexed.stepFiltration (Root := Fin lower) (α := α) (X := ℝ)).le' n
      exact (hdispField.mono hle le_rfl).comp measurable_snd
    change Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        if p.2.length = n then
          z.1 p.1 + Combinatorics.Branching.displaceWith id
            (z.2 p.1) [] p.2 else 0)
    simp only [hp, ↓reduceIte]
    exact hinitial.add hdisp
  · change Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        if p.2.length = n then
          z.1 p.1 + Combinatorics.Branching.displaceWith id
            (z.2 p.1) [] p.2 else 0)
    simp [hp]

private theorem measurable_childrenAtGeneration_over_product
    {Ω Root α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : Ω → Finset (RootIndexed.TreeNode Root α))
    (hparents : Measurable parents)
    (field : Ω → RootIndexed.StepField Root α X) (hfield : Measurable field) :
    Measurable (fun ω => RootIndexed.childrenAtGeneration n (parents ω) (field ω)) := by
  classical
  rw [measurable_set_iff]
  intro q
  by_cases hdepth : q.2.length = n + 1
  · have hnonempty : q.2 ≠ [] := by
      intro h
      simp [h] at hdepth
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hparentDepth : (parent q).2.length = n := by
      simp only [parent]
      rw [List.length_dropLast, hdepth]
      omega
    have hparentMem : Measurable (fun ω => parent q ∈ parents ω) :=
      (measurable_finset_mem (parent q)).comp hparents
    have hsurviveField : MeasurableSet[
        RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)]
        {field : RootIndexed.StepField Root α X |
          Combinatorics.Branching.survive
            (field (parent q).1 (parent q).2) i} :=
      (RootIndexed.step_measurable (X := X) (parent q).1
        (parent q).2 (by omega))
        (Combinatorics.Branching.survive_measurableSet (X := X) i)
    have hsurviveFull : MeasurableSet
        {field : RootIndexed.StepField Root α X |
          Combinatorics.Branching.survive
            (field (parent q).1 (parent q).2) i} :=
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)).le'
        (n + 1) _ hsurviveField
    have hsurvive : Measurable (fun ω => Combinatorics.Branching.survive
        (field ω (parent q).1 (parent q).2) i) := by
      apply measurableSet_setOfPred.mp
      exact hsurviveFull.preimage hfield
    simpa [RootIndexed.childrenAtGeneration, hdepth, hi] using hparentMem.and hsurvive
  · simp [RootIndexed.childrenAtGeneration, hdepth]

private theorem selectedPopulationTotalized_jointInitial_measurable
    {lower : ℕ} {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeDecidableEq : DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeOrder : LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (N H : ℕ) :
    Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun i => z.1 i) id id H z.2) := by
  classical
  induction H with
  | zero => exact measurable_const
  | succ n ih =>
      let field : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ →
          RootIndexed.StepField (Fin lower) α ℝ := Prod.snd
      let parents := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun i => z.1 i) id id n z.2
      let value := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.observedPositionAtGeneration (fun i => z.1 i) id id (n + 1) z.2
      let candidates := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.childrenAtGeneration n (parents z) (field z)
      have hparents : Measurable parents := by
        simpa [parents] using ih
      have hfield : Measurable field := measurable_snd
      have hcandidates : Measurable candidates := by
        exact measurable_childrenAtGeneration_over_product n parents hparents
          field hfield
      -- `TreeNode` is a product type, so its generic product preorder can
      -- otherwise be chosen when elaborating the lexicographic value key.
      -- Use the explicit particle order required by first-`N` selection.
      letI : Preorder (RootIndexed.TreeNode (Fin lower) α) :=
        (inferInstance : LinearOrder (RootIndexed.TreeNode (Fin lower) α)).toPreorder
      have hkey : ∀ p q : RootIndexed.TreeNode (Fin lower) α,
          Measurable fun z =>
            Combinatorics.Branching.Selection.NSelection.valueKey
              (value z) q <
                Combinatorics.Branching.Selection.NSelection.valueKey
                  (value z) p := by
        intro p q
        exact ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.measurable_valueKey_lt
          value (fun r => by
            simpa [value] using observedPosition_jointInitial_measurable (n + 1) r) p q
      change Measurable (fun z =>
        ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.selectFirstNFromSetTotalized
          N (value) candidates z)
      exact ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.measurable_selectFirstNFromSetTotalized
        N value candidates hcandidates hkey

/-- Fixed-horizon first-`N` selection after a successful restart endpoint.
The selected population is a measurable function of the retained endpoint
positions and the fresh descendant field; the preceding joint-law theorem
therefore gives its distribution from those positions. The horizon `H` is a
fixed natural number, not the random time remaining in the original process. -/
theorem selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite
    {Root α : Type*} {lower : ℕ} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (fresh : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField (Fin lower) α ℝ)
    (hpair : Measurable (fun field => (positions field, fresh field)))
    (hjoint : ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
      (fun field => (positions field, fresh field)) =
        (((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
          (RootIndexed.stepFieldLaw (Root := Fin lower) μ))
    (N H : ℕ) :
    ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
        (fun field => RootIndexed.selectedPopulationTotalized N Finset.univ
          (positions field) id id H (fresh field)) =
      ((((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
        (RootIndexed.stepFieldLaw (Root := Fin lower) μ)).map
          (fun p => RootIndexed.selectedPopulationTotalized N Finset.univ
            p.1 id id H p.2) := by
  have hselected : Measurable (fun p : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ p.1 id id H p.2) :=
    selectedPopulationTotalized_jointInitial_measurable N H
  have hpop := selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite
    μ E positions fresh
    hpair
    (fun p : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ =>
      RootIndexed.selectedPopulationTotalized N Finset.univ p.1 id id H p.2)
    hjoint
    hselected
  simpa using hpop

/-- Concrete fixed-horizon population law at the successful endpoint.
The endpoint positions need only be measurable in the stopping-time domain
flow. On the finite endpoint event, the first-`N` population grown for a
fixed number of generations from the actual rank-installed endpoint roots has
the law obtained from those positions and a fresh product field. -/
theorem selectedReserveSpineRestartEndpointPopulation_law_on_finite
    {Root α : Type*} (lower : ℕ) [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeDecidableEq : DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeOrder : LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root)
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (hpositions : Measurable[
      (selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r).measurableSpace] positions)
    (H : ℕ) :
    let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
    (P.restrict {field | τ field ≠ ⊤}).map
      (fun field => @RootIndexed.selectedPopulationTotalized
        (Fin lower) α ℝ ℝ ℝ instFinTreeDecidableEq instFinTreeOrder
        (inferInstance : LinearOrder ℝ) (inferInstance : AddCommMonoid ℝ)
        N Finset.univ (positions field) id id H
        (RootIndexed.selectedSubtreeStepFieldVector
          (fun field i => (Sum.inr r,
            (selectedReserveSpineRestartEndpointRankVector N initialPosition
              R growth hR hgrowth lower upper duration r field i).2)) field)) =
    (((P.restrict {field | τ field ≠ ⊤}).map positions).prod Q).map
      (fun p => @RootIndexed.selectedPopulationTotalized
        (Fin lower) α ℝ ℝ ℝ instFinTreeDecidableEq instFinTreeOrder
        (inferInstance : LinearOrder ℝ) (inferInstance : AddCommMonoid ℝ)
        N Finset.univ p.1 id id H p.2) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode (Fin lower) α) := instFinTreeDecidableEq
  letI : LinearOrder (RootIndexed.TreeNode (Fin lower) α) := instFinTreeOrder
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hτ := selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin lower) μ
  let E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ) := {field | τ field ≠ ⊤}
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let roots : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower →
      (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α := fun field i =>
    (Sum.inr r, (target field i).2)
  let fresh := fun field => RootIndexed.selectedSubtreeStepFieldVector roots field
  have hsumSingleton : ∀ z : Root ⊕ Root,
      MeasurableSet ({z} : Set (Root ⊕ Root)) := by
    intro z
    cases z with
    | inl x =>
        rw [show ({Sum.inl x} : Set (Root ⊕ Root)) =
          Sum.inl '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inl_image
    | inr x =>
        rw [show ({Sum.inr x} : Set (Root ⊕ Root)) =
          Sum.inr '' ({x} : Set Root) by ext y; simp]
        exact (measurableSet_singleton x).inr_image
  letI : MeasurableSingletonClass (Root ⊕ Root) := ⟨hsumSingleton⟩
  have hτmeas : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)) τ := by
    simpa [τ] using hτ
  have htarget : Measurable[hτmeas.measurableSpace] target := by
    simpa [target, hτmeas] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hrootsStop : Measurable[hτmeas.measurableSpace] roots := by
    letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
      hτmeas.measurableSpace
    apply measurable_pi_iff.mpr
    intro i
    have hi : Measurable[hτmeas.measurableSpace] (fun field => target field i) :=
      (measurable_pi_apply i).comp htarget
    exact measurable_const.prodMk (hnodePath.comp hi)
  have hrootsFull : Measurable roots := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hrootsStop.mono hle le_rfl
  have hcount : (Set.range roots).Countable := by
    let encode : (Fin lower → RootIndexed.TreeNode Root α) →
        Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
      fun v i => (Sum.inr r, (v i).2)
    have hsubset : Set.range roots ⊆ Set.range encode := by
      rintro q ⟨field, rfl⟩
      exact ⟨target field, rfl⟩
    exact (Set.countable_range encode).mono hsubset
  have hfresh : Measurable fresh := by
    change Measurable (fun field => RootIndexed.subtreeStepFieldVector
      (roots field) field)
    exact measurable_subtreeStepFieldVector_of_measurable_roots roots hrootsFull hcount
  have hpositionsFull : Measurable positions := by
    have hle : hτmeas.measurableSpace ≤
        (inferInstance : MeasurableSpace
          (RootIndexed.StepField (Root ⊕ Root) α ℝ)) :=
      hτmeas.measurableSpace_le'.trans (iSup_le_iff.mpr fun n =>
        (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)).le n)
    exact hpositions.mono hle le_rfl
  have hpair : Measurable (fun field => (positions field, fresh field)) :=
    hpositionsFull.prodMk hfresh
  have hjoint := selectedReserveSpineRestartEndpointPositionFreshField_jointLaw_on_finite
    hnodePath μ hnorm N initialPosition R growth hR hgrowth lower upper duration
    hupper hbounded hcapacity r positions hpositions
  have hpop := selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite
    μ E positions fresh hpair hjoint N H
  simpa [τ, P, Q, E, roots, fresh] using hpop

end ProbabilityTheory.BranchingRandomWalk

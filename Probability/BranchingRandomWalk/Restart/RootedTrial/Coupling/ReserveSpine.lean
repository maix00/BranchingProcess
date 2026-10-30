/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.ReservePath
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.CapStopped
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.RootIndexed.CapStopped
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Candidates
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import Probability.BranchingRandomWalk.Coupling.Field.Position
public import MeasureTheory.Selection.NSelection.AtRank
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Reserve-spine coupling with first-`N` selection

## Public declarations

* `selectedReserveSpineRestartSourceOnLeft` pulls the causal reserve source back along the
  left coordinate of a two-root pre-sampled field.
* `selectedReserveSpineRestartSourceOnLeft_finiteSlices` and
  `selectedReserveSpineRestartSourceOnLeft_toFinset` state that every finite slice exists and
  equals the original source slice on the left coordinate.
* `selectedReserveSpineRestartSourceOnLeft_card_le` gives the deterministic bound
  `|sourceSlice n| ≤ 1 + (duration + 1) * (2 * cap)`.
* `selectedReserveSpineRestartSourceOnLeft_initialInjection` gives the initial cloud injection
  from the singleton-root population into the rank-installed population.
* `selectedReserveSpineRestartCoupledInjection_ae` gives, almost surely, a cloud injection
  from the reserve-source population to the first-`N` rank-installed population.
* `selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidate_success_ae` and
  `selectedReserveSpineRestartCoupledPopulation_card_ge_of_candidateSuccessEvent_ae` transfer
  a successful candidate's lower cardinality to the rank-installed population.
* `selectedReserveSpineRestartCoupled_position_witness_ae` matches every reserve-source
  particle with a particle at a weakly smaller position;
  `selectedReserveSpineRestartCoupledCandidate_position_witness_ae` gives the same comparison
  for every particle in a successful cap-stopped candidate.
* `selectedReserveSpineFirstSuccess_endpointComparison_ae` states that finite first success
  has a candidate index `k` and completion time `n = k + 1 + duration`, with the lower
  population bound and the particlewise position comparison at that endpoint.

Candidate activation is determined by the reserve spine alone, independently of earlier
candidate outcomes. The endpoint stopping-time and fresh-field laws are in
`Completion/Endpoint.lean` and `Completion/EndpointHorizon.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
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
      ProbabilityTheory.Process.Stopping.Concurrent.Finite.population, ProbabilityTheory.Process.Stopping.Concurrent.Finite.component,
      selectedReserveSpineAlive, selectedReserveSpinePath]
  rw [hzero]
  simpa [RootIndexed.selectedPopulationTotalized] using
    (ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.initialPopulationSliceDominatingMap_of_subset
      id id initialPosition {r} {r} (by intro q hq; exact hq)
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
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_ofPred_eq] at hsuccess
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
    simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_ofPred_eq] at hsuccess
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
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_ofPred_eq] at hsuccessMem
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


end ProbabilityTheory.BranchingRandomWalk

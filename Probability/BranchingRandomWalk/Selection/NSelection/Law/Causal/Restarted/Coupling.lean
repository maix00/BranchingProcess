/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Lemmas.Coupling
import Probability.BranchingRandomWalk.Coupling.Field.Position

/-!
# Coupling a restarted killed population to first-N selection

## Public declarations

- `RootIndexed.restartedRealPositionCoupling` constructs a coupling of two
  copies of the step-field product law using the restarted source and its
  rank-installed matched field.
- `RootIndexed.restartedRealPositionCoupledInjection_ae` states that, almost
  surely, a capacity-bounded restarted source slice admits a slice-dominating
  injection into the matched first-`N` population, under boundary
  normalization of the offspring law.
- `RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae` specializes
  that result to the initial population of a finite root set and its measurable
  restart windows.

For the source slice \(S_n(\omega)\), matched target field \(V_n(\omega)\),
and selected target slice \(T_n(\omega)\), the coupling has both marginals
equal to the step-field law. Under boundary normalization and
\(#S_{k+1}(\omega)\le N\) for \(k<n\), almost surely there is an injection
\(\iota_n:S_n(\omega)\to T_n(\omega)\) satisfying
\[
  \operatorname{position}_{V_n(\omega)}(\iota_n(p))
    \le \operatorname{position}_{\mathrm{left}}(p)
  \quad\text{for every }p\in S_n(\omega).
\]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The canonical product-law coupling for a restarted real-valued killed
population.  Spatial domination is a separate pathwise theorem about this
coupling; it is not built into the definition of a coupling. -/
noncomputable def RootIndexed.restartedRealPositionCoupling
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α Mark)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) :
    ProbabilityTheory.Coupling
      (RootIndexed.stepFieldLaw (Root := Root) μ)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  let source := RootIndexed.restartedRealPositionSource initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper
  exact RootIndexed.causalPopulationCoupling μ N roots initialPosition d hd
    id measurable_id source
    (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
      initial hinitialDepth cutoff window hwindow upper hupper) n

/-- For a real-valued offspring law with boundary normalization, the
rank-installed target satisfies the first-`N` specification almost surely.
Consequently the restarted-source injection is available almost surely on
the capacity event. Bad raw fields, including fields with infinitely many
low-position children, are handled by the totalized selector and lie in the
null exceptional set supplied by `Admissible.Real`. -/
theorem RootIndexed.restartedRealPositionCoupledInjection_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (source : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hsourceFinite : source.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition id (hsourceFinite.toFinset) 0 field)) ())
    (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      (∀ k < n, (hsourceFinite.toFinset (k + 1) field).card ≤ N) →
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field))
            (hsourceFinite.toFinset n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionMatchedField N roots
                initialPosition id (hsourceFinite.toFinset) n field))
            (RootIndexed.restartedRealPositionMatchedPopulation N roots
              initialPosition id (hsourceFinite.toFinset) n field)) ()) := by
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  have hspec := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hnorm N roots initialPosition
  have hspecField : ∀ᵐ field ∂P, ∀ k,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1)
          (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
            (hsourceFinite.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k
            (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
              (hsourceFinite.toFinset) (k + 1) field))
          (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
            (hsourceFinite.toFinset) (k + 1) field))
        (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
          (k + 1) (RootIndexed.restartedRealPositionMatchedField N roots
            initialPosition id (hsourceFinite.toFinset) (k + 1) field)) := by
    apply ae_all_iff.2
    intro k
    let targetField := RootIndexed.restartedRealPositionMatchedField N roots
      initialPosition id (hsourceFinite.toFinset) (k + 1)
    have hleft : RootIndexed.StepField.left =
        (RootIndexed.StepField.reindex Sum.inl :
          RootIndexed.StepField (Root ⊕ Root) α ℝ →
            RootIndexed.StepField Root α ℝ) := rfl
    have htargetLaw : Measurable targetField ∧
        P.map targetField = RootIndexed.stepFieldLaw (Root := Root) μ := by
      change Measurable
          (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
            (hsourceFinite.toFinset) (k + 1)) ∧
        P.map (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
          (hsourceFinite.toFinset) (k + 1)) = RootIndexed.stepFieldLaw (Root := Root) μ
      simpa only [P, RootIndexed.restartedRealPositionMatchedField, hleft] using
        (RootIndexed.rankInstalledField_causalPopulation_measurable_law
          μ N roots initialPosition id measurable_id id measurable_id source
          hsourceFinite (k + 1))
    have hspecMap : ∀ᵐ sample ∂P.map targetField,
        ∀ j, IsFirstNBy N
          (RootIndexed.observedPositionAtGeneration initialPosition id id (j + 1) sample)
          (Combinatorics.Branching.Population.childrenAtGeneration j
            (RootIndexed.selectedPopulationTotalized N roots initialPosition id id j sample)
            sample)
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
            (j + 1) sample) := by
      rw [htargetLaw.2]
      exact hspec
    have hspecFieldAtStage :=
      MeasureTheory.ae_of_ae_map htargetLaw.1.aemeasurable hspecMap
    filter_upwards [hspecFieldAtStage] with field hstage
    exact hstage k
  filter_upwards [hspecField] with field hspecField
  intro hcapacity
  have hselect : ∀ k < n,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1)
          (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
            (hsourceFinite.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.restartedRealPositionMatchedPopulation N roots
            initialPosition id (hsourceFinite.toFinset) k field)
          (RootIndexed.restartedRealPositionMatchedField N roots initialPosition id
            (hsourceFinite.toFinset) (k + 1) field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots initialPosition id
          (hsourceFinite.toFinset) (k + 1) field) := by
    intro k hk
    rw [RootIndexed.restartedRealPositionMatchedPopulation_stage_stable
      N roots initialPosition id (hsourceFinite.toFinset) k field]
    simpa [RootIndexed.restartedRealPositionMatchedField,
      RootIndexed.restartedRealPositionMatchedPopulation] using hspecField k
  exact ⟨RootIndexed.restartedRealPositionCoupledInjectionOfTotalizedSpecs
    N roots initialPosition id source hsourceFinite initialInjection n field
    hselect hcapacity⟩

/-- Multi-root specialization of the almost-sure restarted coupling. It
starts from the empty address at each root; the only pathwise hypothesis is
that the killed source remains within capacity. -/
theorem RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae
    {Root α : Type*} [Countable α]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      field ∈ (RootIndexed.restartedRealPositionSource initialPosition id
        measurable_id (RootIndexed.initialPopulation (α := α) roots)
        (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff
        window hwindow upper hupper).capacityEvent N n →
        let source := RootIndexed.restartedRealPositionSourceSlice initialPosition id
          measurable_id (RootIndexed.initialPopulation (α := α) roots)
          (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff
          window hwindow upper hupper
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field))
            (source n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionMatchedField N roots
                initialPosition id source n field))
            (RootIndexed.restartedRealPositionMatchedPopulation N roots
              initialPosition id source n field)) ()) := by
  let initial := RootIndexed.initialPopulation (α := α) roots
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    simp [initial, RootIndexed.mem_initialPopulation_iff] at hp
    rcases hp with ⟨r, hr, rfl⟩
    rfl
  let source := RootIndexed.restartedRealPositionSource initialPosition id
    measurable_id initial hinitialDepth cutoff window hwindow upper hupper
  let hsourceFinite := RootIndexed.restartedRealPositionSource_finiteSlices
    initialPosition id measurable_id initial hinitialDepth cutoff
    window hwindow upper hupper
  have hsourceZero (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      hsourceFinite.toFinset 0 field = initial := by
    change RootIndexed.restartedRealPositionSourceSlice initialPosition id
      measurable_id initial hinitialDepth cutoff window hwindow upper hupper
      0 field = initial
    exact RootIndexed.restartedRealPositionSourceSlice_zero initialPosition id
      measurable_id initial hinitialDepth cutoff window hwindow upper hupper field
  have hinitialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition id (hsourceFinite.toFinset) 0 field)) () := by
    intro field
    rw [hsourceZero]
    simpa [RootIndexed.restartedRealPositionMatchedPopulation,
      RootIndexed.restartedRealPositionMatchedField,
      RootIndexed.selectedPopulationTotalized] using
      (ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.initialPopulationSliceDominatingMap_of_subset
        id id initialPosition roots roots (by intro r hr; exact hr)
        (RootIndexed.StepField.left field) (RootIndexed.StepField.right field))
  have hgeneric := RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N roots initialPosition source hsourceFinite hinitialInjection n
  dsimp only
  filter_upwards [hgeneric] with field hgood
  intro hcapacity
  exact hgood (fun k hk =>
    RootIndexed.CausalPopulation.FiniteSlices.card_succ_le_of_mem_capacityEvent
      source hsourceFinite N n (by simpa [source] using hcapacity) k hk)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end

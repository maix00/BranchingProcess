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
# Coupling a restarted selected BRW population to first-\(N\) selection

## Public declarations

- `RootIndexed.restartedRealPositionCoupling` constructs a coupling of two
  copies of the step-field product law using the restarted selected population
  and its rank-installed matched field.
- `RootIndexed.restartedRealPositionCoupledInjection_ae` states that, almost
  surely, a capacity-bounded restarted selected-population slice admits a
  slice-dominating injection into the matched first-`N` population, under boundary
  normalization of the offspring law.
- `RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae` specializes
  that result to the initial population of a finite root set and its measurable
  restart windows.

For the selected-population slice \(P_n(\omega)\), matched field
\(V_n(\omega)\), and first-\(N\) slice \(P_n^{(N)}(\omega)\), the coupling
has both marginals equal to the step-field law. Under boundary normalization
and \(\#P_{k+1}(\omega)\le N\) for \(k<n\), almost surely there is an
injection \(\iota_n:P_n(\omega)\to P_n^{(N)}(\omega)\) satisfying
\[
  \operatorname{position}_{V_n(\omega)}(\iota_n(p))
    \le \operatorname{position}_{\mathrm{left}}(p)
  \quad\text{for every }p\in P_n(\omega).
\]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The canonical product-law coupling for a restarted real-valued selected
BRW population.  Spatial domination is a separate pathwise theorem about this
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
  let selectedBRWPopulation := RootIndexed.restartedRealPositionSelectedBRWPopulation initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper
  exact RootIndexed.causalPopulationCoupling μ N roots initialPosition d hd
    id measurable_id selectedBRWPopulation
    (RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices initialPosition d hd
      initial hinitialDepth cutoff window hwindow upper hupper) n

/-- For a real-valued offspring law with boundary normalization, the
rank-installed first-`N` population satisfies the first-`N` specification
almost surely. Consequently the restarted selected-population injection is
available almost surely on the capacity event. Raw fields with infinitely many
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
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α ℝ) Root α ℝ
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := ℝ))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) 0 field)) ())
    (n : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      (∀ k < n, (hselectedBRWPopulationFiniteSlices.toFinset (k + 1) field).card ≤ N) →
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field))
            (hselectedBRWPopulationFiniteSlices.toFinset n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionNSelectedBRWField N roots
                initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) n field))
            (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
              initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) n field)) ()) := by
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  have hspec := RootIndexed.selectedPopulationTotalized_succ_spec_ae
    μ hnorm N roots initialPosition
  have hspecField : ∀ᵐ field ∂P, ∀ k,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id k
            (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
              (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
          (k + 1) (RootIndexed.restartedRealPositionNSelectedBRWField N roots
            initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field)) := by
    apply ae_all_iff.2
    intro k
    let nSelectedBRWField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
      initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)
    have hleft : RootIndexed.StepField.left =
        (RootIndexed.StepField.reindex Sum.inl :
          RootIndexed.StepField (Root ⊕ Root) α ℝ →
            RootIndexed.StepField Root α ℝ) := rfl
    have hnSelectedBRWFieldLaw : Measurable nSelectedBRWField ∧
        P.map nSelectedBRWField = RootIndexed.stepFieldLaw (Root := Root) μ := by
      change Measurable
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)) ∧
        P.map (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
          (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1)) = RootIndexed.stepFieldLaw (Root := Root) μ
      simpa only [P, RootIndexed.restartedRealPositionNSelectedBRWField, hleft] using
        (RootIndexed.rankInstalledField_causalPopulation_measurable_law
          μ N roots initialPosition id measurable_id id measurable_id selectedBRWPopulation
          hselectedBRWPopulationFiniteSlices (k + 1))
    have hspecMap : ∀ᵐ sample ∂P.map nSelectedBRWField,
        ∀ j, IsFirstNBy N
          (RootIndexed.observedPositionAtGeneration initialPosition id id (j + 1) sample)
          (Combinatorics.Branching.Population.childrenAtGeneration j
            (RootIndexed.selectedPopulationTotalized N roots initialPosition id id j sample)
            sample)
          (RootIndexed.selectedPopulationTotalized N roots initialPosition id id
            (j + 1) sample) := by
      rw [hnSelectedBRWFieldLaw.2]
      exact hspec
    have hspecFieldAtStage :=
      MeasureTheory.ae_of_ae_map hnSelectedBRWFieldLaw.1.aemeasurable hspecMap
    filter_upwards [hspecFieldAtStage] with field hstage
    exact hstage k
  filter_upwards [hspecField] with field hspecField
  intro hselectedBRWPopulationCapacity
  have hnSelectedBRWPopulationFirstN : ∀ k < n,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition id id (k + 1)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
            initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) k field)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
            (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots initialPosition id
          (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field) := by
    intro k hk
    rw [RootIndexed.restartedRealPositionNSelectedBRWPopulation_stage_stable
      N roots initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) k field]
    simpa [RootIndexed.restartedRealPositionNSelectedBRWField,
      RootIndexed.restartedRealPositionNSelectedBRWPopulation] using hspecField k
  exact ⟨RootIndexed.restartedRealPositionCoupledInjectionOfTotalizedSpecs
    N roots initialPosition id selectedBRWPopulation hselectedBRWPopulationFiniteSlices initialInjection n field
    hnSelectedBRWPopulationFirstN hselectedBRWPopulationCapacity⟩

/-- Multi-root specialization of the almost-sure restarted coupling. It
starts from the empty address at each root; the only pathwise hypothesis is
that the selected BRW population remains within capacity. -/
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
      field ∈ (RootIndexed.restartedRealPositionSelectedBRWPopulation initialPosition id
        measurable_id (RootIndexed.initialPopulation (α := α) roots)
        (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff
        window hwindow upper hupper).capacityEvent N n →
        let selectedBRWPopulation := RootIndexed.restartedRealPositionSelectedBRWPopulationSlice initialPosition id
          measurable_id (RootIndexed.initialPopulation (α := α) roots)
          (by simp [RootIndexed.mem_initialPopulation_iff]) cutoff
          window hwindow upper hupper
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.StepField.left field))
            (selectedBRWPopulation n field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              (RootIndexed.restartedRealPositionNSelectedBRWField N roots
                initialPosition id selectedBRWPopulation n field))
            (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
              initialPosition id selectedBRWPopulation n field)) ()) := by
  let initial := RootIndexed.initialPopulation (α := α) roots
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    simp [initial, RootIndexed.mem_initialPopulation_iff] at hp
    rcases hp with ⟨r, hr, rfl⟩
    rfl
  let selectedBRWPopulation := RootIndexed.restartedRealPositionSelectedBRWPopulation initialPosition id
    measurable_id initial hinitialDepth cutoff window hwindow upper hupper
  let hselectedBRWPopulationFiniteSlices := RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices
    initialPosition id measurable_id initial hinitialDepth cutoff
    window hwindow upper hupper
  have hselectedBRWInitialSlice (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
      hselectedBRWPopulationFiniteSlices.toFinset 0 field = initial := by
    change RootIndexed.restartedRealPositionSelectedBRWPopulationSlice initialPosition id
      measurable_id initial hinitialDepth cutoff window hwindow upper hupper
      0 field = initial
    exact RootIndexed.restartedRealPositionSelectedBRWPopulationSlice_zero initialPosition id
      measurable_id initial hinitialDepth cutoff window hwindow upper hupper field
  have hinitialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud id
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition id (hselectedBRWPopulationFiniteSlices.toFinset) 0 field)) () := by
    intro field
    rw [hselectedBRWInitialSlice]
    simpa [RootIndexed.restartedRealPositionNSelectedBRWPopulation,
      RootIndexed.restartedRealPositionNSelectedBRWField,
      RootIndexed.selectedPopulationTotalized] using
      (ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.initialPopulationSliceDominatingMap_of_subset
        id id initialPosition roots roots (by intro r hr; exact hr)
        (RootIndexed.StepField.left field) (RootIndexed.StepField.right field))
  have hgeneric := RootIndexed.restartedRealPositionCoupledInjection_ae
    μ hnorm N roots initialPosition selectedBRWPopulation hselectedBRWPopulationFiniteSlices hinitialInjection n
  dsimp only
  filter_upwards [hgeneric] with field hgood
  intro hselectedBRWPopulationCapacity
  exact hgood (fun k hk =>
    RootIndexed.CausalPopulation.FiniteSlices.card_succ_le_of_mem_capacityEvent
      selectedBRWPopulation hselectedBRWPopulationFiniteSlices N n (by simpa [selectedBRWPopulation] using hselectedBRWPopulationCapacity) k hk)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end

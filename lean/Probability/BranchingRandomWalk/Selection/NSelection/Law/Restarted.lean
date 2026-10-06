/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Law.CausalPopulation
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity
import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real
import Probability.BranchingRandomWalk.Population.Processes.Selected.GenerationUpdate

/-!
# Coupling a restarted killed population to first-N selection

The killed source is constructed from relative-position windows on the left
half of one common pre-sampled field.  Rank installation then produces a
second field with the original product law, on which first-`N` selection is
run.  The result is a measure-level coupling with both marginals verified.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

/-- The restarted killed population, realized on the left half of the common
two-copy pre-sampled field used by rank installation. -/
noncomputable def RootIndexed.restartedRealPositionSource
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left := by
  let killed := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
  have hleft : ∀ k, @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α Mark)
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark) k)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) k)
      RootIndexed.StepField.left := by
    intro k
    rw [show RootIndexed.StepField.left =
      (RootIndexed.StepField.reindex Sum.inl :
        RootIndexed.StepField (Root ⊕ Root) α Mark →
          RootIndexed.StepField Root α Mark) by rfl]
    exact RootIndexed.StepField.reindex_filtration_measurable
      (X := Mark) Sum.inl k
  exact killed.pullback RootIndexed.StepField.left
    hleft
    (by rfl)

theorem RootIndexed.restartedRealPositionSource_finiteSlices
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k)) :
    (RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper).FiniteSlices := by
  intro n field
  unfold RootIndexed.restartedRealPositionSource
  rw [RootIndexed.CausalPopulation.pullback_population]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    initialPosition d hd initial hinitialDepth cutoff window hwindow upper hupper
    n (RootIndexed.StepField.left field)

/-- The finite presentation of one killed source slice used by the concrete
first-`N` coupling algorithm.  Finiteness remains a theorem about the
set-valued source rather than part of the population type. -/
noncomputable def RootIndexed.restartedRealPositionSourceSlice
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  (RootIndexed.restartedRealPositionSource_finiteSlices initialPosition d hd
    initial hinitialDepth cutoff window hwindow upper hupper).toFinset n field

@[simp] theorem RootIndexed.mem_restartedRealPositionSourceSlice
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (p : RootIndexed.TreeNode Root α) :
    p ∈ RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field ↔
    p ∈ RootIndexed.restartedRealPositionSource initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field :=
  RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset _ _ _ _

@[simp] theorem RootIndexed.restartedRealPositionSource_zero
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionSource initialPosition d hd initial
        hinitialDepth cutoff window hwindow upper hupper 0 field = initial := by
  unfold RootIndexed.restartedRealPositionSource
  rw [RootIndexed.CausalPopulation.pullback_population]
  ext p
  simp [
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets,
    RootIndexed.CausalPopulation.ofPredicate]

@[simp] theorem RootIndexed.restartedRealPositionSourceSlice_zero
    {Root α Mark : Type*}
    [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ k, MeasurableSet (window k))
    (upper : ℕ → ℝ) (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionSourceSlice initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper 0 field = initial := by
  ext p
  simp

/-- The finite rank-installed target field for a restarted source. The target
population uses the totalized selector, so this construction is defined even
on raw fields where a first-`N` segment does not exist. -/
noncomputable def RootIndexed.restartedRealPositionMatchedField
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α)) :
    ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      RootIndexed.StepField Root α Mark :=
  RootIndexed.rankInstalledField
    (fun k field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      (RootIndexed.StepField.left field) p)
    (fun k _ field p => RootIndexed.observedPositionAtGeneration initialPosition d id k
      field p)
    source
    (fun k _ field => RootIndexed.selectedPopulationTotalized N roots
      initialPosition d id k field)
    RootIndexed.StepField.left RootIndexed.StepField.right

/-- The first-`N` target population evaluated on its finite rank-installed
field. -/
noncomputable def RootIndexed.restartedRealPositionMatchedPopulation
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    Finset (RootIndexed.TreeNode Root α) :=
  RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
    (RootIndexed.restartedRealPositionMatchedField N roots initialPosition d
      source n field)

theorem RootIndexed.restartedRealPositionMatchedPopulation_stage_stable
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionMatchedPopulation N roots initialPosition d
        source n field =
      RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
        (RootIndexed.restartedRealPositionMatchedField N roots initialPosition d
          source (n + 1) field) := by
  change RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
      (RootIndexed.restartedRealPositionMatchedField N roots initialPosition d
        source n field) =
    RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
      (RootIndexed.restartedRealPositionMatchedField N roots initialPosition d
        source (n + 1) field)
  rw [RootIndexed.restartedRealPositionMatchedField,
    RootIndexed.rankInstalledField_succ]
  exact (RootIndexed.selectedPopulationTotalized_updateGeneration_of_le
    N roots initialPosition d id n n le_rfl _ _).symm

/-- The finite-stage restarted rank installation gives a pathwise injection
whenever the first-`N` specification holds on the actual target stages used by
the recursion. The premise is local to this sample and these stages; it does
not quantify over unrelated raw fields. -/
noncomputable def RootIndexed.restartedRealPositionCoupledInjectionOfTotalizedSpecs
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (source : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (hsourceFinite : source.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition d (hsourceFinite.toFinset) 0 field)) ())
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (hselect : ∀ k < n,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id (k + 1)
          (RootIndexed.restartedRealPositionMatchedField N roots
            initialPosition d (hsourceFinite.toFinset) (k + 1) field))
        (RootIndexed.childrenAtGeneration k
          (RootIndexed.restartedRealPositionMatchedPopulation N roots
            initialPosition d (hsourceFinite.toFinset) k field)
          (RootIndexed.restartedRealPositionMatchedField N roots
            initialPosition d (hsourceFinite.toFinset) (k + 1) field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition d (hsourceFinite.toFinset) (k + 1) field))
    (hcapacity : ∀ k < n,
      (hsourceFinite.toFinset (k + 1) field).card ≤ N) :
    Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hsourceFinite.toFinset n field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.restartedRealPositionMatchedField N roots
            initialPosition d (hsourceFinite.toFinset) n field))
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition d (hsourceFinite.toFinset) n field)) () := by
  classical
  induction n with
  | zero =>
      simpa [RootIndexed.restartedRealPositionMatchedField,
        RootIndexed.restartedRealPositionMatchedPopulation,
        RootIndexed.rankInstalledField] using initialInjection field
  | succ n ih =>
      have hinj := ih
        (fun k hk => hselect k (Nat.lt_succ_of_lt hk))
        (fun k hk => hcapacity k (Nat.lt_succ_of_lt hk))
      let sourceWalk := RootIndexed.BranchingWalk.ofStepField initialPosition
        (RootIndexed.StepField.left field)
      let priorField := RootIndexed.restartedRealPositionMatchedField N roots
        initialPosition d (hsourceFinite.toFinset) n field
      let nextField := RootIndexed.restartedRealPositionMatchedField N roots
        initialPosition d (hsourceFinite.toFinset) (n + 1) field
      let sourceParents := hsourceFinite.toFinset n field
      let targetParents := RootIndexed.restartedRealPositionMatchedPopulation N roots
        initialPosition d (hsourceFinite.toFinset) n field
      let canonical :=
        Combinatorics.Branching.Selection.Coupling.canonicalInjection id d sourceWalk
          (RootIndexed.BranchingWalk.ofStepField initialPosition priorField)
          sourceParents targetParents hinj
      have hcard : sourceParents.card ≤ targetParents.card :=
        Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
          id d sourceWalk
          (RootIndexed.BranchingWalk.ofStepField initialPosition priorField)
          sourceParents targetParents hinj
      have htargetParentsDepth : ∀ q ∈ targetParents, q.2.length = n := by
        intro q hq
        exact RootIndexed.selectedPopulationTotalized_depth N roots initialPosition
          d id n priorField q (by
            simpa [targetParents, priorField,
              RootIndexed.restartedRealPositionMatchedPopulation] using hq)
      have hcanonical {p : RootIndexed.TreeNode Root α} (hp : p ∈ sourceParents) :
          canonical p = Combinatorics.Branching.Selection.NSelection.matchByRankOrSelf
            (RootIndexed.observedPositionAtGeneration initialPosition d id n
              (RootIndexed.StepField.left field))
            (RootIndexed.observedPositionAtGeneration initialPosition d id n priorField)
            sourceParents targetParents hcard p := by
        have hsourceValue : ∀ q ∈ sourceParents,
            id (sourceWalk.position d q.1 q.2) =
              RootIndexed.observedPositionAtGeneration initialPosition d id n
                (RootIndexed.StepField.left field) q := by
          intro q hq
          exact (RootIndexed.observedPositionAtGeneration_eq initialPosition d id n
            (RootIndexed.StepField.left field) q
            (source.depth n field q
              ((hsourceFinite.mem_toFinset n field q).mp hq))).symm
        have htargetValue : ∀ q ∈ targetParents,
            id ((RootIndexed.BranchingWalk.ofStepField initialPosition
              priorField).position d q.1 q.2) =
              RootIndexed.observedPositionAtGeneration initialPosition d id n
                priorField q := by
          intro q hq
          exact (RootIndexed.observedPositionAtGeneration_eq initialPosition d id n
            priorField q (htargetParentsDepth q hq)).symm
        rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
        exact Combinatorics.Branching.Selection.NSelection.matchByRankOrSelf_congr_of_eqOn
          sourceParents targetParents hcard hp hsourceValue htargetValue
      let hparents : Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            sourceWalk sourceParents)
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            (RootIndexed.BranchingWalk.ofStepField initialPosition nextField)
            targetParents) () := {
        toFun := canonical
        mapsTo := canonical.mapsTo
        injOn := canonical.injOn
        dominates := by
          intro p hp
          change (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d (canonical p).1 (canonical p).2 ≤
            sourceWalk.position d p.1 p.2
          have hdepth : (canonical p).2.length = n := by
            apply RootIndexed.selectedPopulationTotalized_depth N roots
              initialPosition d id n priorField (canonical p)
            simpa [targetParents, priorField,
              RootIndexed.restartedRealPositionMatchedPopulation,
              Combinatorics.Branching.Selection.Coupling.populationCloud] using
              canonical.mapsTo hp
          have hpos : (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d (canonical p).1 (canonical p).2 =
            (RootIndexed.BranchingWalk.ofStepField initialPosition
              priorField).position d (canonical p).1 (canonical p).2 := by
            change (RootIndexed.BranchingWalk.ofStepField initialPosition
                (RootIndexed.StepField.updateGeneration n _ priorField)).position
                  d (canonical p).1 (canonical p).2 = _
            exact Combinatorics.Branching.RootIndexed.BranchingWalk.position_updateGeneration_of_le
              d n initialPosition _ priorField
                (canonical p).1 (canonical p).2 (by omega)
          rw [hpos]
          exact canonical.dominates p hp }
      have hstep {p : RootIndexed.TreeNode Root α} (hp : p ∈ sourceParents) :
          nextField (canonical p).1 (canonical p).2 =
            RootIndexed.StepField.left field p.1 p.2 := by
        change RootIndexed.rankInstalledField
          (fun k sample q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k (RootIndexed.StepField.left sample) q)
          (fun k _ β q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k β q)
          (hsourceFinite.toFinset)
          (fun k _ β => RootIndexed.selectedPopulationTotalized N roots
            initialPosition d id k β)
          RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) field
          (canonical p).1 (canonical p).2 = _
        rw [hcanonical hp]
        exact RootIndexed.rankInstalledField_succ_apply_matchByRankOrSelf
          (fun k sample q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k (RootIndexed.StepField.left sample) q)
          (fun k _ β q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k β q)
          (hsourceFinite.toFinset)
          (fun k _ β => RootIndexed.selectedPopulationTotalized N roots
            initialPosition d id k β)
          RootIndexed.StepField.left RootIndexed.StepField.right n field hcard
          htargetParentsDepth
          hp
      have hselected : IsFirstNBy N
          (fun q => ((RootIndexed.BranchingWalk.ofStepField initialPosition
            nextField).position d q.1 q.2))
          (Combinatorics.Branching.Selection.Coupling.offspringAddressSet
            (↑targetParents)
            (fun p => {i | survive (nextField p.1 p.2) i}))
          (RootIndexed.restartedRealPositionMatchedPopulation N roots
            initialPosition d (hsourceFinite.toFinset) (n + 1) field) := by
        have hspec := hselect n (Nat.lt_succ_self n)
        have hchildren := RootIndexed.childrenAtGeneration_eq_offspringAddressSet
          n targetParents nextField htargetParentsDepth
        have hvalue : Set.EqOn
            (RootIndexed.observedPositionAtGeneration initialPosition d id
              (n + 1) nextField)
            (fun q => (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d q.1 q.2)
            (RootIndexed.childrenAtGeneration n
              targetParents nextField) := by
          intro q hq
          exact RootIndexed.observedPositionAtGeneration_eq initialPosition d id
            (n + 1) nextField q
            (RootIndexed.childrenAtGeneration_depth n targetParents nextField q hq)
        have hspec' := hspec.congr_value hvalue
        rw [hchildren] at hspec'
        simpa only [nextField, targetParents,
          RootIndexed.restartedRealPositionMatchedPopulation] using hspec'
      have hretained : ↑(hsourceFinite.toFinset (n + 1) field) ⊆
          Combinatorics.Branching.Selection.Coupling.offspringAddressSet
            (↑(hsourceFinite.toFinset n field))
            (fun p => Combinatorics.Branching.support
              (RootIndexed.StepField.left field p.1 p.2)) := by
        simpa only [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset] using
          source.successor n field
      have hslots : ∀ p ∈ sourceParents,
          Combinatorics.Branching.support
              (RootIndexed.StepField.left field p.1 p.2) ⊆
            {i | survive (nextField (canonical p).1 (canonical p).2) i} := by
        intro p hp i hi
        have hsame := hstep hp
        rw [hsame]
        simpa [Combinatorics.Branching.support] using hi
      have hsharedIncrement : ∀ p ∈ sourceParents, ∀ i ∈
          Combinatorics.Branching.support
            (RootIndexed.StepField.left field p.1 p.2),
          value' (((RootIndexed.BranchingWalk.ofStepField initialPosition
            nextField).step (canonical p).1 (canonical p).2).map d) i =
          value' ((sourceWalk.step p.1 p.2).map d) i := by
        intro p hp i hi
        have hsame := hstep hp
        change value' ((nextField (canonical p).1 (canonical p).2).map d) i =
          value' ((RootIndexed.StepField.left field p.1 p.2).map d) i
        rw [hsame]
      exact Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
        id d N sourceWalk
        (RootIndexed.BranchingWalk.ofStepField initialPosition nextField)
        sourceParents targetParents
        (fun p => Combinatorics.Branching.support
          (RootIndexed.StepField.left field p.1 p.2))
        (fun p => {i | survive (nextField p.1 p.2) i})
        (hsourceFinite.toFinset (n + 1) field)
        (RootIndexed.restartedRealPositionMatchedPopulation N roots
          initialPosition d (hsourceFinite.toFinset) (n + 1) field)
        hretained (hcapacity n (Nat.lt_succ_self n)) hselected hparents
        hslots hsharedIncrement
        (fun _ _ z hle => by simpa using add_le_add_right hle z)

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
        (RootIndexed.childrenAtGeneration k
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
          (RootIndexed.childrenAtGeneration j
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
        (RootIndexed.childrenAtGeneration k
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
      (RootIndexed.initialPopulationInjection id id roots initialPosition
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

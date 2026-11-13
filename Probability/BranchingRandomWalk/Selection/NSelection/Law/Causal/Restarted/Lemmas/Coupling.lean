/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Basic
import Probability.BranchingRandomWalk.Coupling.Field.Position
import Combinatorics.UlamHarris.Basic
import Mathlib.Basic.Countable.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Defs.LinearOrder
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Basic
import Probability.BranchingRandomWalk.Population.Processes.Selected.RootIndexed

/-!
# Internal lemmas for the restarted coupling

This module contains the one-use pathwise induction used by the public
restarted-coupling conclusions. Its declarations are imported by
`Restarted/Coupling.lean` and do not form a separate result interface.

## Internal proof declarations

- `RootIndexed.restartedRealPositionSelectedBRWPopulationSlice_zero` proves that the initial
  slice equals the initial finite population.
- `RootIndexed.restartedRealPositionNSelectedBRWPopulation_stage_stable` identifies
  the population at generation `n` using matched fields through stages `n` and
  `n + 1`.
- `RootIndexed.restartedRealPositionCoupledInjectionOfTotalizedSpecs` proves
  the finite-stage slice injection by induction, assuming the first-`N`
  specification along the actual first-`N` stages and capacity bounds for the
  selected-population slices.

Write (P_n) for the selected-population slice, (V_n) for the matched field,
and (P_n^{(N)}) for the totalized first-`N` slice.  The identities used are
\[
  P_n^{(N)} = \operatorname{SelectedPopulationTotalized}(N,V_{n+1}),
\]
and the induction establishes
\[
  \left(\forall k<n,\; \#P_{k+1}\le N\right)
    \land \left(\forall k<n,\; \operatorname{FirstN}_k\right)
  \Longrightarrow
  \exists\,\iota_n:P_n\hookrightarrow P_n^{(N)}.
\]
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

@[simp] lemma RootIndexed.restartedRealPositionSelectedBRWPopulationSlice_zero
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
    RootIndexed.restartedRealPositionSelectedBRWPopulationSlice initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper 0 field = initial := by
  apply Finset.coe_injective
  rw [RootIndexed.restartedRealPositionSelectedBRWPopulationSlice,
    RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
  simp [RootIndexed.restartedRealPositionSelectedBRWPopulation,
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets,
    RootIndexed.CausalPopulation.ofPredicate,
    RootIndexed.CausalPopulation.selectedBy]

lemma RootIndexed.restartedRealPositionNSelectedBRWPopulation_stage_stable
    {Root α Mark : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    (d : Mark → ℝ)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark) :
    RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots initialPosition d
        selectedBRWPopulation n field =
      RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
        (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
          selectedBRWPopulation (n + 1) field) := by
  change RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
        selectedBRWPopulation n field) =
    RootIndexed.selectedPopulationTotalized N roots initialPosition d id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition d
        selectedBRWPopulation (n + 1) field)
  rw [RootIndexed.restartedRealPositionNSelectedBRWField,
    RootIndexed.rankInstalledField_succ]
  exact (RootIndexed.selectedPopulationTotalized_updateGeneration_of_le
    N roots initialPosition d id n n le_rfl _ _).symm

/-- The finite-stage restarted rank installation gives a pathwise injection
whenever the first-`N` specification holds on the actual first-`N` BRW stages used by
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
    (selectedBRWPopulation : RootIndexed.CausalPopulation
      (RootIndexed.StepField (Root ⊕ Root) α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := Mark))
      RootIndexed.StepField.left)
    (hselectedBRWPopulationFiniteSlices : selectedBRWPopulation.FiniteSlices)
    (initialInjection : ∀ field, Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset 0 field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.right field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) 0 field)) ())
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α Mark)
    (hnSelectedBRWPopulationFirstN : ∀ k < n,
      IsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initialPosition d id (k + 1)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots
            initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (Combinatorics.Branching.Population.childrenAtGeneration k
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
            initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) k field)
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots
            initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (k + 1) field))
    (hselectedBRWPopulationCapacity : ∀ k < n,
      (hselectedBRWPopulationFiniteSlices.toFinset (k + 1) field).card ≤ N) :
    Cloud.SliceDominatingMap id
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.StepField.left field))
        (hselectedBRWPopulationFiniteSlices.toFinset n field))
      (Combinatorics.Branching.Selection.Coupling.populationCloud d
        (RootIndexed.BranchingWalk.ofStepField initialPosition
          (RootIndexed.restartedRealPositionNSelectedBRWField N roots
            initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) n field))
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) n field)) () := by
  classical
  induction n with
  | zero =>
      simpa [RootIndexed.restartedRealPositionNSelectedBRWField,
        RootIndexed.restartedRealPositionNSelectedBRWPopulation,
        RootIndexed.rankInstalledField] using initialInjection field
  | succ n ih =>
      have hinj := ih
        (fun k hk => hnSelectedBRWPopulationFirstN k (Nat.lt_succ_of_lt hk))
        (fun k hk => hselectedBRWPopulationCapacity k (Nat.lt_succ_of_lt hk))
      let selectedBRW := RootIndexed.BranchingWalk.ofStepField initialPosition
        (RootIndexed.StepField.left field)
      let priorField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
        initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) n field
      let nextField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
        initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (n + 1) field
      let selectedBRWPopulationParents := hselectedBRWPopulationFiniteSlices.toFinset n field
      let nSelectedBRWPopulationParents := RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
        initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) n field
      let canonical :=
        Combinatorics.Branching.Selection.Coupling.canonicalInjection id d selectedBRW
          (RootIndexed.BranchingWalk.ofStepField initialPosition priorField)
          selectedBRWPopulationParents nSelectedBRWPopulationParents hinj
      have hcard : selectedBRWPopulationParents.card ≤ nSelectedBRWPopulationParents.card :=
        Combinatorics.Branching.Selection.Coupling.population_card_le_of_injection
          id d selectedBRW
          (RootIndexed.BranchingWalk.ofStepField initialPosition priorField)
          selectedBRWPopulationParents nSelectedBRWPopulationParents hinj
      have hnSelectedBRWPopulationParentsDepth : ∀ q ∈ nSelectedBRWPopulationParents, q.2.length = n := by
        intro q hq
        exact RootIndexed.selectedPopulationTotalized_depth N roots initialPosition
          d id n priorField q (by
            simpa [nSelectedBRWPopulationParents, priorField,
              RootIndexed.restartedRealPositionNSelectedBRWPopulation] using hq)
      have hcanonical {p : RootIndexed.TreeNode Root α} (hp : p ∈ selectedBRWPopulationParents) :
          canonical p = Combinatorics.Selection.NSelection.matchByRankOrSelf
            (RootIndexed.observedPositionAtGeneration initialPosition d id n
              (RootIndexed.StepField.left field))
            (RootIndexed.observedPositionAtGeneration initialPosition d id n priorField)
            selectedBRWPopulationParents nSelectedBRWPopulationParents hcard p := by
        have hselectedBRWPopulationOrderKey : ∀ q ∈ selectedBRWPopulationParents,
            id (selectedBRW.position d q.1 q.2) =
              RootIndexed.observedPositionAtGeneration initialPosition d id n
                (RootIndexed.StepField.left field) q := by
          intro q hq
          exact (RootIndexed.observedPositionAtGeneration_eq initialPosition d id n
            (RootIndexed.StepField.left field) q
            (selectedBRWPopulation.depth n field q
              ((hselectedBRWPopulationFiniteSlices.mem_toFinset n field q).mp hq))).symm
        have hnSelectedPopulationOrderKey : ∀ q ∈ nSelectedBRWPopulationParents,
            id ((RootIndexed.BranchingWalk.ofStepField initialPosition
              priorField).position d q.1 q.2) =
              RootIndexed.observedPositionAtGeneration initialPosition d id n
                priorField q := by
          intro q hq
          exact (RootIndexed.observedPositionAtGeneration_eq initialPosition d id n
            priorField q (hnSelectedBRWPopulationParentsDepth q hq)).symm
        rw [Combinatorics.Branching.Selection.Coupling.canonicalInjection_apply]
        exact Combinatorics.Selection.NSelection.matchByRankOrSelf_congr_of_eqOn
          selectedBRWPopulationParents nSelectedBRWPopulationParents hcard hp hselectedBRWPopulationOrderKey hnSelectedPopulationOrderKey
      let hparents : Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            selectedBRW selectedBRWPopulationParents)
          (Combinatorics.Branching.Selection.Coupling.populationCloud d
            (RootIndexed.BranchingWalk.ofStepField initialPosition nextField)
            nSelectedBRWPopulationParents) () := {
        toFun := canonical
        mapsTo := canonical.mapsTo
        injOn := canonical.injOn
        dominates := by
          intro p hp
          change (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d (canonical p).1 (canonical p).2 ≤
            selectedBRW.position d p.1 p.2
          have hdepth : (canonical p).2.length = n := by
            apply RootIndexed.selectedPopulationTotalized_depth N roots
              initialPosition d id n priorField (canonical p)
            simpa [nSelectedBRWPopulationParents, priorField,
              RootIndexed.restartedRealPositionNSelectedBRWPopulation,
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
      have hstep {p : RootIndexed.TreeNode Root α} (hp : p ∈ selectedBRWPopulationParents) :
          nextField (canonical p).1 (canonical p).2 =
            RootIndexed.StepField.left field p.1 p.2 := by
        change RootIndexed.rankInstalledField
          (fun k sample q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k (RootIndexed.StepField.left sample) q)
          (fun k _ β q => RootIndexed.observedPositionAtGeneration
            initialPosition d id k β q)
          (hselectedBRWPopulationFiniteSlices.toFinset)
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
          (hselectedBRWPopulationFiniteSlices.toFinset)
          (fun k _ β => RootIndexed.selectedPopulationTotalized N roots
            initialPosition d id k β)
          RootIndexed.StepField.left RootIndexed.StepField.right n field hcard
          hnSelectedBRWPopulationParentsDepth
          hp
      have hselected : IsFirstNBy N
          (fun q => ((RootIndexed.BranchingWalk.ofStepField initialPosition
            nextField).position d q.1 q.2))
          (Combinatorics.Branching.Population.offspringAddressSet
            (↑nSelectedBRWPopulationParents)
            (fun p => {i | survive (nextField p.1 p.2) i}))
          (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
            initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (n + 1) field) := by
        have hspec := hnSelectedBRWPopulationFirstN n (Nat.lt_succ_self n)
        have hchildren := Combinatorics.Branching.Population.childrenAtGeneration_eq_offspringAddressSet
          n nSelectedBRWPopulationParents nextField hnSelectedBRWPopulationParentsDepth
        have hvalue : Set.EqOn
            (RootIndexed.observedPositionAtGeneration initialPosition d id
              (n + 1) nextField)
            (fun q => (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d q.1 q.2)
            (Combinatorics.Branching.Population.childrenAtGeneration n
              nSelectedBRWPopulationParents nextField) := by
          intro q hq
          exact RootIndexed.observedPositionAtGeneration_eq initialPosition d id
            (n + 1) nextField q
            (Combinatorics.Branching.Population.childrenAtGeneration_depth n nSelectedBRWPopulationParents nextField q hq)
        have hspec' := hspec.congr_value hvalue
        rw [hchildren] at hspec'
        simpa only [nextField, nSelectedBRWPopulationParents,
          RootIndexed.restartedRealPositionNSelectedBRWPopulation] using hspec'
      have hretained : ↑(hselectedBRWPopulationFiniteSlices.toFinset (n + 1) field) ⊆
          Combinatorics.Branching.Population.offspringAddressSet
            (↑(hselectedBRWPopulationFiniteSlices.toFinset n field))
            (fun p => Combinatorics.Branching.support
              (RootIndexed.StepField.left field p.1 p.2)) := by
        simpa only [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset] using
          selectedBRWPopulation.successor n field
      have hselectedBRWPopulationChildSlots_subset_survival : ∀ p ∈ selectedBRWPopulationParents,
          Combinatorics.Branching.support
              (RootIndexed.StepField.left field p.1 p.2) ⊆
            {i | survive (nextField (canonical p).1 (canonical p).2) i} := by
        intro p hp i hi
        have hsame := hstep hp
        rw [hsame]
        simpa [Combinatorics.Branching.support] using hi
      have hmatchedBRWParents_sharedIncrement : ∀ p ∈ selectedBRWPopulationParents, ∀ i ∈
          Combinatorics.Branching.support
            (RootIndexed.StepField.left field p.1 p.2),
          value' (((RootIndexed.BranchingWalk.ofStepField initialPosition
            nextField).step (canonical p).1 (canonical p).2).map d) i =
          value' ((selectedBRW.step p.1 p.2).map d) i := by
        intro p hp i hi
        have hsame := hstep hp
        change value' ((nextField (canonical p).1 (canonical p).2).map d) i =
          value' ((RootIndexed.StepField.left field p.1 p.2).map d) i
        rw [hsame]
      exact Combinatorics.Branching.Selection.Coupling.nextGenerationInjection_of_isFirstNBy
        id d N selectedBRW
        (RootIndexed.BranchingWalk.ofStepField initialPosition nextField)
        selectedBRWPopulationParents nSelectedBRWPopulationParents
        (fun p => Combinatorics.Branching.support
          (RootIndexed.StepField.left field p.1 p.2))
        (fun p => {i | survive (nextField p.1 p.2) i})
        (hselectedBRWPopulationFiniteSlices.toFinset (n + 1) field)
        (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
          initialPosition d (hselectedBRWPopulationFiniteSlices.toFinset) (n + 1) field)
        hretained (hselectedBRWPopulationCapacity n (Nat.lt_succ_self n)) hselected hparents
        hselectedBRWPopulationChildSlots_subset_survival hmatchedBRWParents_sharedIncrement
        (fun _ _ z hle => by simpa using add_le_add_right hle z)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end

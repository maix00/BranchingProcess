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

- `RootIndexed.restartedRealPositionSourceSlice_zero` proves that the initial
  slice equals the initial finite population.
- `RootIndexed.restartedRealPositionMatchedPopulation_stage_stable` identifies
  the population at generation `n` using matched fields through stages `n` and
  `n + 1`.
- `RootIndexed.restartedRealPositionCoupledInjectionOfTotalizedSpecs` proves
  the finite-stage slice injection by induction, assuming the first-`N`
  specification along the actual target stages and capacity bounds for the
  source slices.

Writing (S_n) for the source slice, (V_n) for the matched field, and
(T_n) for the totalized selected target, the identities used are
\[
  T_n = \operatorname{SelectedPopulationTotalized}(N,V_{n+1}),
  \qquad
  \left(\forall k<n,\; \#S_{k+1}\le N\right)
    \land \left(\forall k<n,\; \operatorname{FirstN}_k\right)
  \Longrightarrow
  \exists\,\iota_n:S_n\hookrightarrow T_n.
\]
-/

section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

@[simp] lemma RootIndexed.restartedRealPositionSourceSlice_zero
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
  apply Finset.coe_injective
  rw [RootIndexed.restartedRealPositionSourceSlice,
    RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
  simp [RootIndexed.restartedRealPositionSource,
    RootIndexed.CausalPopulation.ofRestartedRealPositionSets,
    RootIndexed.CausalPopulation.ofPredicate,
    RootIndexed.CausalPopulation.selectedBy]

lemma RootIndexed.restartedRealPositionMatchedPopulation_stage_stable
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
        (Combinatorics.Branching.Population.childrenAtGeneration k
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
          canonical p = Combinatorics.Selection.NSelection.matchByRankOrSelf
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
        exact Combinatorics.Selection.NSelection.matchByRankOrSelf_congr_of_eqOn
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
          (Combinatorics.Branching.Population.offspringAddressSet
            (↑targetParents)
            (fun p => {i | survive (nextField p.1 p.2) i}))
          (RootIndexed.restartedRealPositionMatchedPopulation N roots
            initialPosition d (hsourceFinite.toFinset) (n + 1) field) := by
        have hspec := hselect n (Nat.lt_succ_self n)
        have hchildren := Combinatorics.Branching.Population.childrenAtGeneration_eq_offspringAddressSet
          n targetParents nextField htargetParentsDepth
        have hvalue : Set.EqOn
            (RootIndexed.observedPositionAtGeneration initialPosition d id
              (n + 1) nextField)
            (fun q => (RootIndexed.BranchingWalk.ofStepField initialPosition
              nextField).position d q.1 q.2)
            (Combinatorics.Branching.Population.childrenAtGeneration n
              targetParents nextField) := by
          intro q hq
          exact RootIndexed.observedPositionAtGeneration_eq initialPosition d id
            (n + 1) nextField q
            (Combinatorics.Branching.Population.childrenAtGeneration_depth n targetParents nextField q hq)
        have hspec' := hspec.congr_value hvalue
        rw [hchildren] at hspec'
        simpa only [nextField, targetParents,
          RootIndexed.restartedRealPositionMatchedPopulation] using hspec'
      have hretained : ↑(hsourceFinite.toFinset (n + 1) field) ⊆
          Combinatorics.Branching.Population.offspringAddressSet
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end

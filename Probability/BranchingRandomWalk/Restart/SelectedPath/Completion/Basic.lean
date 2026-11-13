/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.Population
public import Probability.Process.Stopping.Selection.Ranked
public import MeasureTheory.Selection.NSelection.ByValue
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic

/-!
# Endpoint data for the causal selected-path restart

## Public declarations

* `Restart.SelectedPath.Completion.time` is the first successful candidate's completion
  time pulled back to the common two-root field.
* `Restart.SelectedPath.Completion.time_isStoppingTime` proves that this completion time
  is a stopping time for the joint domain filtration.
* `Restart.SelectedPath.Completion.endpointNodesByRank` lists the first `lower` particles of the
  rank-installed first-`N` BRW population at that time, with the root sentinel used if the time is infinite
  or a requested rank is absent.
* `Restart.SelectedPath.Completion.endpointNodesByRank_measurable` proves measurability of that
  vector with respect to the endpoint stopping-time σ-algebra.

For the common field \(f\), the endpoint generation is
\[
  \tau(f)=\operatorname{Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion}
    (R,\mathrm{growth},r)(\operatorname{left}(f)).
\]
The endpoint vector is the rank vector at this time, with sentinel \((r,[])\):
\[
  V(f)=\operatorname{particleRankVectorAtStoppingTime}
    (\tau,\operatorname{position},\operatorname{population},\mathrm{lower},(r,[]))(f).
\]
At a finite \(\tau(f)=n\), its \(i\)-th coordinate is the particle of rank \(i\)
in the rank-installed generation-\(n\) population. Here position and population
denote the generation-indexed position map and candidate set of that
rank-installed first-\(N\) process.

The fallback roots associated with the selected-path BRW population and the factorization proof stages are grouped under
`Completion/Lemmas/EndpointHorizon/`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion

open Combinatorics.Branching Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

/-- The first-success completion time viewed on the common two-root field.
Candidate times and success events are pulled back from the left copy, so the
time remains adapted to the joint domain filtration. -/
noncomputable def time
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    RootIndexed.StepField (Root ⊕ Root) α ℝ → WithTop ℕ :=
  fun field => Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion
    R growth hR lower upper duration r (RootIndexed.StepField.left field)

theorem time_isStoppingTime
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ))
      (Restart.SelectedPath.Completion.time R growth hR hgrowth
        lower upper duration r) := by
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let G := RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ)
  let τ := Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion
    R growth hR lower upper duration r
  have hτ : IsStoppingTime G τ :=
    Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion_isStoppingTime
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
rank-installed first-`N` BRW particles by their ordinary finite-generation spatial
rank. The vector is totalized if completion never occurs or the requested
rank is absent. -/
noncomputable def endpointNodesByRank
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
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  exact particleRankVectorAtStoppingTime
    (Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        hselectedBRWPopulation.toFinset n field) p)
    (fun n field => RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
      initialPosition id hselectedBRWPopulation.toFinset n field)
    lower (r, []) field

/-- The concrete first-`N` BRW endpoint vector is measurable in the stopped domain
filtration. Its stagewise candidate population is the selected population on
the recursively rank-installed field; the preceding choices and their spatial
keys are measurable at the generations that reveal them. -/
theorem endpointNodesByRank_measurable
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
    Measurable[(Restart.SelectedPath.Completion.time_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition R growth
        hR hgrowth lower upper duration r) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let τ := Restart.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  let Restart.SelectedPath.Population.family :=
    Restart.SelectedPath.Population.leftBRWFamily R growth hR hgrowth upper duration r
  let selectedBRWOrderKey := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let nSelectedBRWOrderKey := fun k (_ : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k field p
  let selectedBRWPopulation := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) =>
    hselectedBRWPopulation.toFinset k field
  let nSelectedBRWPopulation := fun k (_ : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (field : RootIndexed.StepField Root α ℝ) =>
    RootIndexed.selectedPopulationTotalized N {r} initialPosition id id k field
  have hselectedBRWPopulationDepth : ∀ k field p, p ∈ selectedBRWPopulation k field → p.2.length = k := by
    intro k field p hp
    exact Restart.SelectedPath.Population.family.depth k field p
      ((hselectedBRWPopulation.mem_toFinset k field p).mp hp)
  have hselectedBRWPopulationFiber : ∀ k s, MeasurableSet[F k]
      {field | selectedBRWPopulation k field = s} := by
    intro k s
    exact (hselectedBRWPopulation.measurable_toFinset k) (measurableSet_singleton s)
  have hselectedBRWPopulationRange : ∀ k, (Set.range (selectedBRWPopulation k)).Countable :=
    fun _ => Set.to_countable _
  have hselectedBRWOrderKeyMeasurable : ∀ k p q, Measurable[F k]
      fun field => valueKey (selectedBRWOrderKey k field) q < valueKey (selectedBRWOrderKey k field) p := by
    intro k p q
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F k
    apply Combinatorics.Selection.NSelection.measurable_valueKey_lt
    intro z
    exact (RootIndexed.positionAtGeneration_measurable initialPosition id
      measurable_id k z.1 z.2).comp
        (RootIndexed.StepField.reindex_filtration_measurable Sum.inl k)
  have hstage : ∀ n,
      (Set.range (RootIndexed.rankInstalledBlockChoice
        selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation n)).Countable ∧
      ∀ choices, MeasurableSet[F n]
        {field | RootIndexed.rankInstalledBlockChoice selectedBRWOrderKey nSelectedBRWOrderKey
          selectedBRWPopulation nSelectedBRWPopulation n field = choices} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hpriorCount : ∀ k, k < n → (Set.range
            (RootIndexed.rankInstalledBlockChoice selectedBRWOrderKey nSelectedBRWOrderKey
              selectedBRWPopulation nSelectedBRWPopulation k)).Countable := fun k hk => (ih k hk).1
        have hpriorFiber : ∀ k, k < n → ∀ choices,
            MeasurableSet[RootIndexed.stepFiltration
              (Root := Root ⊕ Root) (α := α) (X := ℝ) k]
              {field | RootIndexed.rankInstalledBlockChoice selectedBRWOrderKey nSelectedBRWOrderKey
                selectedBRWPopulation nSelectedBRWPopulation k field = choices} :=
          fun k hk => (ih k hk).2
        have hnSelectedBRWPopulationMeas : Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            (fun field => nSelectedBRWPopulation n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
          by
            simpa [nSelectedBRWPopulation] using
              (RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
                N {r} initialPosition id measurable_id id measurable_id
                selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n
                hpriorCount hpriorFiber)
        have hnSelectedBRWPopulationFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            {field | nSelectedBRWPopulation n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
          fun s => hnSelectedBRWPopulationMeas (measurableSet_singleton s)
        have hnSelectedBRWPopulationRange : (Set.range fun field => nSelectedBRWPopulation n field
            (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
              RootIndexed.StepField.left RootIndexed.StepField.right n field)
            ).Countable := Set.to_countable _
        have hnSelectedBRWPopulationKey : ∀ p q, Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
            fun field => valueKey (nSelectedBRWOrderKey n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
              valueKey (nSelectedBRWOrderKey n field
                (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                  RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
          let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) :=
            RootIndexed.stepFiltration
              (Root := Root ⊕ Root) (α := α) (X := ℝ) n
          intro p q
          exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
            (fun field z => nSelectedBRWOrderKey n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field) z)
            (fun z => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
              initialPosition id measurable_id id measurable_id selectedBRWOrderKey nSelectedBRWOrderKey
              selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n hpriorCount hpriorFiber z) p q
        constructor
        · exact RootIndexed.rankBlockChoice_range_countable_of_supports n
            (selectedBRWOrderKey n)
            (fun field => nSelectedBRWOrderKey n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (selectedBRWPopulation n)
            (fun field => nSelectedBRWPopulation n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (hselectedBRWPopulationRange n) hnSelectedBRWPopulationRange
        · intro choices
          exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
            (selectedBRWOrderKey n)
            (fun field => nSelectedBRWOrderKey n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (selectedBRWPopulation n)
            (fun field => nSelectedBRWPopulation n field
              (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
                RootIndexed.StepField.left RootIndexed.StepField.right n field))
            (hselectedBRWPopulationFiber n) (hselectedBRWPopulationRange n) hnSelectedBRWPopulationFiber hnSelectedBRWPopulationRange
            (hselectedBRWOrderKeyMeasurable n) hnSelectedBRWPopulationKey choices
  have hnSelectedBRWPopulationMeas (n : ℕ) : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := ℝ) n]
      (fun field => nSelectedBRWPopulation n field
        (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) :=
    by
      simpa [nSelectedBRWPopulation] using
        (RootIndexed.selectedPopulationTotalized_rankInstalledField_measurable_of_lt
          N {r} initialPosition id measurable_id id measurable_id selectedBRWOrderKey nSelectedBRWOrderKey
          selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n
          (fun k hk => (hstage k).1) (fun k hk => (hstage k).2))
  have hnSelectedBRWPopulationFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n]
        {field | nSelectedBRWPopulation n field
          (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field) = s} :=
    hnSelectedBRWPopulationMeas n (measurableSet_singleton s)
  have hnSelectedBRWPopulationRange (n : ℕ) : (Set.range fun field => nSelectedBRWPopulation n field
      (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
      ).Countable := Set.to_countable _
  have hnSelectedBRWPopulationKey (n : ℕ) : ∀ p q, Measurable[F n]
      fun field => valueKey (nSelectedBRWOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (nSelectedBRWOrderKey n field
          (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p := by
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F n
    intro p q
    exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
      (fun field z => nSelectedBRWOrderKey n field
        (RootIndexed.rankInstalledField selectedBRWOrderKey nSelectedBRWOrderKey selectedBRWPopulation nSelectedBRWPopulation
          RootIndexed.StepField.left RootIndexed.StepField.right n field) z)
      (fun z => RootIndexed.observedPosition_rankInstalledField_measurable_of_lt
        initialPosition id measurable_id id measurable_id selectedBRWOrderKey nSelectedBRWOrderKey
        selectedBRWPopulation nSelectedBRWPopulation hselectedBRWPopulationDepth n
        (fun k hk => (hstage k).1) (fun k hk => (hstage k).2) z) p q
  let candidates := fun n field =>
    RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} initialPosition id
      hselectedBRWPopulation.toFinset n field
  let value := fun n field p =>
    RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        hselectedBRWPopulation.toFinset n field) p
  have hcandidateFiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n] {field | candidates n field = s} := by
    simpa [candidates, nSelectedBRWPopulation, RootIndexed.restartedRealPositionNSelectedBRWPopulation,
      RootIndexed.restartedRealPositionNSelectedBRWField, selectedBRWPopulation, selectedBRWOrderKey, nSelectedBRWOrderKey]
      using hnSelectedBRWPopulationFiber n s
  have hcandidateRange (n : ℕ) : (Set.range (candidates n)).Countable :=
    Set.to_countable _
  have hkey (n : ℕ) (p q : RootIndexed.TreeNode Root α) : Measurable[F n]
      fun field => valueKey (value n field) q < valueKey (value n field) p := by
    simpa [value, nSelectedBRWOrderKey, RootIndexed.restartedRealPositionNSelectedBRWField,
      selectedBRWPopulation, selectedBRWOrderKey, nSelectedBRWOrderKey] using hnSelectedBRWPopulationKey n p q
  have hτ : IsStoppingTime F τ := by
    simpa [τ, Restart.SelectedPath.Completion.time] using
      Restart.SelectedPath.Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r
  have hmeas := measurable_particleRankVectorAtStoppingTime F τ hτ
    value candidates hcandidateFiber hcandidateRange hkey lower (r, [])
  change Measurable[(Restart.SelectedPath.Completion.time_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
    (particleRankVectorAtStoppingTime τ value candidates lower (r, []))
  exact hmeas


end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion

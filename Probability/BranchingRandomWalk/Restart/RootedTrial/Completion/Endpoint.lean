/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
public import Probability.Process.Stopping.Selection.Ranked
public import MeasureTheory.Selection.NSelection.ByValue
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic

/-!
# Endpoint data for the causal reserve-spine restart

## Public declarations

* `selectedReserveSpineRestartEndpointTime` is the first successful candidate's completion
  time pulled back to the common two-root field.
* `selectedReserveSpineRestartEndpointTime_isStoppingTime` proves that this completion time
  is a stopping time for the joint domain filtration.
* `selectedReserveSpineRestartEndpointRankVector` lists the first `lower` particles of the
  rank-installed population at that time, with the root sentinel used if the time is infinite
  or a requested rank is absent.
* `selectedReserveSpineRestartEndpointRankVector_measurable` proves measurability of that
  vector with respect to the endpoint stopping-time σ-algebra.

For the common field \(f\), the endpoint generation is
\[
  \tau(f)=\operatorname{selectedReserveSpineFirstSuccessfulCandidateCompletion}
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

The source-side fallback roots and the factorization proof stages are grouped under
`Completion/Lemmas/EndpointHorizon/`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

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
    apply Combinatorics.Selection.NSelection.measurable_valueKey_lt
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
          exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
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
    exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
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


end ProbabilityTheory.BranchingRandomWalk

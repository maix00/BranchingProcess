/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Offspring

public import Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.ReservePath
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Spine.Splits
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.CapStopped
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.RootIndexed.CapStopped
public import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Candidates
public import Probability.Process.HittingTime.OrderedCandidates

/-!
# Causal reserve candidates on one pre-sampled spine

The candidates are indexed by the generation of their reserve parent.  Their
enablement only uses the spine and split mark observed at that generation;
the fixed candidate windows are independent of the success/failure outcomes.

## Public declarations

* selectedReserveSpineCandidateEnabled_adapted and
  selectedReserveSpineCandidatePopulation_adapted place candidate activation and its
  generation population in the domain filtration at generation $n$.
* `mem_selectedReserveSpineCandidatePopulation_iff` characterizes candidate
  membership by an enabled split index and membership in that index's
  cap-stopped trial.
* `selectedReserveSpineCandidateSuccessEvent` is the event that candidate $k$ is
  enabled and its fixed-duration cap-stopped population reaches the target size;
  `selectedReserveSpineCandidateSuccessEvent_measurable` places this event at
  generation $k+1+\mathrm{duration}$.
* `selectedReserveSpineFirstSuccessfulCandidateCompletion` records the first
  successful candidate's completion generation, and
  `selectedReserveSpineFirstSuccessfulCandidateCompletion_isStoppingTime` states that
  \[
    \{\tau\le n\}
      = \bigcup_{\substack{k\in\mathbb N\\k+1+\mathrm{duration}\le n}}
        \{\text{candidate }k\text{ succeeds}\}.
  \]
* `selectedReserveSpineRestartBRWPopulationSlice` and
  `selectedReserveSpineRestartBRWPopulation` define the reserve-spine BRW
  population formed by the spine particle and all enabled candidate
  populations through generation \(n\);
  selectedReserveSpineRestartBRWPopulation_finiteSlices and
  selectedReserveSpineRestartBRWPopulation_card_le give finite-slice existence and the bound
  \[
    |P_n^{\mathrm{reserve}}|
      \le 1+(\mathrm{duration}+1)(2\,\mathrm{cap}).
  \]
* `selectedReserveSpineRestartBRWPopulationSlice_contains_live_spine` states that
  on the alive event, the population slice contains the address pair
  $(r,\operatorname{selectedReserveSpinePath}(R,r,n,\omega))$.
* `selectedReserveSpineCandidate_subset_restartBRWPopulation_at_endpoint` embeds an enabled
  candidate at its completion generation;
  `selectedReserveSpineRestartBRWPopulation_card_ge_of_candidate_success`
  transfers its endpoint population lower bound to the reserve-spine BRW
  population slice.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The split-generation index set is observable at the current generation.
The mark at spine generation `k` first enters the domain filtration at `k+1`.
-/
theorem selectedReserveSpineCandidateEnabled_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (duration n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => selectedReserveSpineCandidateEnabled R r duration n ω) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  apply (@measurable_finset_iff ℕ (RootIndexed.StepField Root α X) (F n)).2
  intro k
  have toPropMeasurable (p : RootIndexed.StepField Root α X → Prop)
      (hs : MeasurableSet[F n] {ω | p ω}) :
      @Measurable (RootIndexed.StepField Root α X) Prop (F n) inferInstance
        p := by
    exact (@measurableSet_setOfPred _ (F n) p).mp hs
  by_cases hk : k < n
  · by_cases hwindow : n ≤ k + 1 + duration
    · have halive : MeasurableSet[F n]
          {ω | selectedReserveSpineAlive R r k ω} :=
        F.mono (Nat.le_of_lt hk) _
          (selectedReserveSpineAlive_measurable R hR r k)
      have hmark : MeasurableSet[F (k + 1)]
          {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} := by
        have hstep : Measurable[F (k + 1)]
            (fun ω => ω r (selectedReserveSpinePath R r k ω)) := by
          exact selectedReserveSpineMark_adapted R hR r k
        exact (splitBy_measurable R hR).preimage hstep
      have hmark' : MeasurableSet[F n]
          {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} :=
        F.mono (by omega) _ hmark
      have heq : {ω | k ∈ selectedReserveSpineCandidateEnabled
          R r duration n ω} =
          {ω | selectedReserveSpineAlive R r k ω} ∩
            {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} := by
        ext ω
        simp [selectedReserveSpineCandidateEnabled, hk, hwindow,
          Finset.mem_filter, Finset.mem_range]
      apply toPropMeasurable _
      rw [heq]
      exact halive.inter hmark'
    · have heq : {ω | k ∈ selectedReserveSpineCandidateEnabled
          R r duration n ω} = ∅ := by
        ext ω
        simp [selectedReserveSpineCandidateEnabled, hk, hwindow,
          Finset.mem_filter, Finset.mem_range]
      apply toPropMeasurable _
      simp [heq]
  · have heq : {ω | k ∈ selectedReserveSpineCandidateEnabled
        R r duration n ω} = ∅ := by
      ext ω
      simp [selectedReserveSpineCandidateEnabled, hk,
        Finset.mem_filter, Finset.mem_range]
    apply toPropMeasurable _
    simp [heq]

/-- The finite-window population of candidate subtrees is adapted.  At a
split in generation `k`, the first-child trial starts in generation `k+1`.
-/
theorem selectedReserveSpineCandidatePopulation_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root] [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => selectedReserveSpineCandidatePopulation
        R growth hR cap duration r n ω) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let lineages : RootIndexed.ReserveLineages Root PUnit.{1} α X :=
    selectedReserveSpineLineages R hR
  let enabled := fun n ω => selectedReserveSpineCandidateEnabled R r duration n ω
  have henabled : ∀ n s, MeasurableSet[F n] {ω | enabled n ω = s} := by
    intro n s
    exact (measurableSet_singleton s).preimage
      (selectedReserveSpineCandidateEnabled_adapted R hR r duration n)
  have henabledRange : ∀ n, (Set.range (enabled n)).Countable := by
    intro n
    exact Set.to_countable _
  let start : ℕ → RootIndexed.StepField Root α X → WithTop ℕ :=
    fun i _ => ((i + 1 : ℕ) : WithTop ℕ)
  let candidate : ℕ → ℕ → ℕ → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α) :=
    fun _ k age ω => lineages.capStoppedCandidate R growth cap r PUnit.unit k age ω
  have hstart : ∀ i : ℕ, IsStoppingTime F (start i) := by
    intro i
    exact isStoppingTime_const F (i + 1)
  have hcandidate : ∀ i k age, Measurable[F (k + age)] (candidate i k age) := by
    intro i k age
    simpa [candidate] using lineages.capStoppedCandidate_adapted
      R growth hR hgrowth cap r PUnit.unit k age
  have hcomponent : ∀ i n, Measurable[F n]
      (ProbabilityTheory.Process.Stopping.Concurrent.Finite.component start candidate i n) := by
    intro i n
    exact ProbabilityTheory.Process.Stopping.Concurrent.Finite.component_adapted F start hstart candidate
      hcandidate i n
  have hpop : ∀ n, Measurable[F n]
      (fun ω => ProbabilityTheory.Process.Stopping.Concurrent.Finite.population enabled start candidate n ω) :=
    ProbabilityTheory.Process.Stopping.Concurrent.Finite.population_adapted F enabled start candidate
      henabled henabledRange hcomponent
  intro n
  simpa [selectedReserveSpineCandidatePopulation, lineages, enabled,
    selectedReserveSpineLineages, start, candidate] using hpop n

/-- The success event for a fixed split generation on the pre-sampled reserve
spine. It is indexed before looking at any trial outcome, and includes the
spine-survival and split conditions needed for the first child to be an
actual candidate. -/
noncomputable def selectedReserveSpineCandidateSuccessEvent
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (lower upper duration : ℕ) (r : Root) (k : ℕ) :
    Set (RootIndexed.StepField Root α X) :=
  {ω | selectedReserveSpineAlive R r k ω ∧
    ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R ∧
    growthTrialSuccess growth lower upper duration
      (fun v =>
        let q := (selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
          R r PUnit.unit (k + 1) ω
        ω q.1 (q.2 ++ v))}

/-- A fixed reserve-spine candidate's success is observable at its fixed
completion generation. The random first-child address is selected from the
pre-sampled field by a measurable root selector. -/
theorem selectedReserveSpineCandidateSuccessEvent_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (r : Root) (k : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (k + 1 + duration)]
      (selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let lineages := selectedReserveSpineLineages (Root := Root) R hR
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    lineages.firstChildRootAt R r PUnit.unit (k + 1)
  have hchosen : ∀ p, MeasurableSet[F (k + 1)] {ω | chosen ω = p} := by
    intro p
    exact lineages.firstChildRootAt_fiber_measurable R hR r PUnit.unit
      (k + 1) p
  have hcount : (Set.range chosen).Countable := by
    have hnode : (Set.range (fun ω => (chosen ω).2)).Countable :=
      Set.to_countable _
    apply hnode.image (fun u => (r, u)) |>.mono
    rintro p ⟨ω, rfl⟩
    have hroot : (chosen ω).1 = r := by
      exact lineages.firstChildRootAt_root R r PUnit.unit (k + 1) ω
    have hpair : (r, (chosen ω).2) = chosen ω := by
      apply Prod.ext
      · exact hroot.symm
      · rfl
    exact ⟨(chosen ω).2, ⟨ω, rfl⟩, hpair⟩
  have hdepth : ∀ ω, (chosen ω).2.length = k + 1 := by
    intro ω
    exact lineages.firstChildRootAt_depth R r PUnit.unit (k + 1) ω
  have hsuccess : MeasurableSet[F (k + 1 + duration)]
      {ω | growthTrialSuccess growth lower upper duration
        (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))} :=
    RootIndexed.growthTrialSuccessAt_selectedRoot_measurable growth hgrowth
      (k + 1) duration lower upper chosen hchosen hcount hdepth
  have halive : MeasurableSet[F k]
      {ω | selectedReserveSpineAlive R r k ω} :=
    selectedReserveSpineAlive_measurable R hR r k
  have halive' : MeasurableSet[F (k + 1 + duration)]
      {ω | selectedReserveSpineAlive R r k ω} :=
    F.mono (by omega) _ halive
  have hmark : MeasurableSet[F (k + 1)]
      {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} := by
    exact (splitBy_measurable R hR).preimage
      (selectedReserveSpineMark_adapted R hR r k)
  have hmark' : MeasurableSet[F (k + 1 + duration)]
      {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} :=
    F.mono (by omega) _ hmark
  change MeasurableSet[F (k + 1 + duration)]
    ({ω | selectedReserveSpineAlive R r k ω} ∩
      ({ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} ∩
        {ω | growthTrialSuccess growth lower upper duration
          (fun v => ω (chosen ω).1 ((chosen ω).2 ++ v))}))
  exact halive'.inter (hmark'.inter hsuccess)

/-- The first successful candidate's completion generation. Candidates are
tested in their preassigned split-generation order; the chosen index depends
on success, but the candidate family and all trial windows do not. -/
noncomputable def selectedReserveSpineFirstSuccessfulCandidateCompletion
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (lower upper duration : ℕ) (r : Root) :
    RootIndexed.StepField Root α X → WithTop ℕ :=
  firstDeclaredSuccess fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k}

/-- The first successful candidate completion is a stopping time in the
domain filtration. At generation `n`, only the finitely many candidate
windows ending by `n` enter the event `{T ≤ n}`. -/
theorem selectedReserveSpineFirstSuccessfulCandidateCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (r : Root) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
        lower upper duration r) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  let completion : ℕ → RootIndexed.StepField Root α X → WithTop ℕ :=
    fun k _ => ((k + 1 + duration : ℕ) : WithTop ℕ)
  let success : ℕ → Set (RootIndexed.StepField Root α X) :=
    fun k => selectedReserveSpineCandidateSuccessEvent R growth hR
      lower upper duration r k
  have hobservable : CandidateObservable F completion success := by
    intro k n
    by_cases htime : k + 1 + duration = n
    · have hcast : ((k + 1 + duration : ℕ) : WithTop ℕ) = n :=
        congrArg (fun m : ℕ => (m : WithTop ℕ)) htime
      have htest : MeasurableSet[F (k + 1 + duration)] (success k) := by
        simpa [success] using selectedReserveSpineCandidateSuccessEvent_measurable
          R growth hR hgrowth lower upper duration r k
      have htest' : MeasurableSet[F n] (success k) := by
        rw [← htime]
        exact htest
      have heq : {ω | completion k ω = n ∧ ω ∈ success k} = success k := by
        ext ω
        simp only [Set.mem_ofPred_eq, completion]
        constructor
        · rintro ⟨_, hω⟩
          exact hω
        · intro hω
          exact ⟨hcast, hω⟩
      rw [heq]
      exact htest'
    · have hcastne : ((k + 1 + duration : ℕ) : WithTop ℕ) ≠ n := by
        intro h
        exact htime (WithTop.coe_injective h)
      have heq : {ω | completion k ω = n ∧ ω ∈ success k} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
          completion, not_and]
        intro h
        exact False.elim (hcastne h)
      rw [heq]
      exact F n |>.measurableSet_empty
  simpa [selectedReserveSpineFirstSuccessfulCandidateCompletion,
    completion, success] using
      (first_candidate_completion_isStoppingTime F completion success hobservable)

/-- The candidate-union slice at generation `n`, represented as a finite set.
The reserve spine contributes at most one particle; each enabled split
generation contributes its cap-stopped first-child trial.
-/
noncomputable def selectedReserveSpineRestartBRWPopulationSlice
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Finset (RootIndexed.TreeNode Root α) :=
  (if selectedReserveSpineAlive R r n ω then
      {(r, selectedReserveSpinePath R r n ω)} else ∅) ∪
    selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω

/-- The active reserve spine is one of the addresses in the candidate-union
selected BRW slice. -/
theorem selectedReserveSpineRestartBRWPopulationSlice_contains_live_spine
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r n ω) :
    (r, selectedReserveSpinePath R r n ω) ∈
      selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r n ω := by
  simp [selectedReserveSpineRestartBRWPopulationSlice, halive]

/-- Membership in the finite-window candidate union is exactly membership in
one enabled, fixed-start cap-stopped candidate. -/
theorem mem_selectedReserveSpineCandidatePopulation_iff
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) (q : RootIndexed.TreeNode Root α) :
    q ∈ selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω ↔
      ∃ k ∈ selectedReserveSpineCandidateEnabled R r duration n ω,
        q ∈ (selectedReserveSpineLineages R hR).capStoppedCandidate
          R growth cap r PUnit.unit (k + 1) (n - (k + 1)) ω := by
  classical
  rw [selectedReserveSpineCandidatePopulation,
    ProbabilityTheory.Process.Stopping.Concurrent.Finite.mem_population_iff]
  constructor
  · rintro ⟨k, hk, hq⟩
    have hk' : k < n := by
      change k ∈ (Finset.range n).filter _ at hk
      exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hcomponent := ProbabilityTheory.Process.Stopping.Concurrent.Finite.component_eq_of_start
      (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
      (fun i j age ω =>
        (selectedReserveSpineLineages R hR).capStoppedCandidate
          R growth cap r PUnit.unit j age ω)
      k ω (Nat.succ_le_of_lt hk') rfl
    rw [hcomponent] at hq
    exact ⟨k, hk, hq⟩
  · rintro ⟨k, hk, hq⟩
    have hk' : k < n := by
      change k ∈ (Finset.range n).filter _ at hk
      exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    have hcomponent := ProbabilityTheory.Process.Stopping.Concurrent.Finite.component_eq_of_start
      (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
      (fun i j age ω =>
        (selectedReserveSpineLineages R hR).capStoppedCandidate
          R growth cap r PUnit.unit j age ω)
      k ω (Nat.succ_le_of_lt hk') rfl
    refine ⟨k, hk, ?_⟩
    rw [hcomponent]
    exact hq

/-- Depth of an enabled candidate slice, with its absolute start generation
made explicit. -/
private theorem selectedReserveSpineCandidate_node_depth
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) (q : RootIndexed.TreeNode Root α)
    (hq : q ∈ selectedReserveSpineCandidatePopulation R growth hR
      cap duration r n ω) : q.2.length = n := by
  obtain ⟨k, hk, hq⟩ :=
    (mem_selectedReserveSpineCandidatePopulation_iff R growth hR
      cap duration r n ω q).mp hq
  have hk' : k < n := by
    change k ∈ (Finset.range n).filter _ at hk
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hrootDepth := (selectedReserveSpineLineages R hR).firstChildRootAt_depth
    R r PUnit.unit (k + 1) ω
  have hqDepth := rootedCapStoppedPopulation_node_depth growth cap ω
    ((selectedReserveSpineLineages R hR).firstChildRootAt R r PUnit.unit
      (k + 1) ω) q (n - (k + 1)) hq
  rw [hrootDepth] at hqDepth
  omega

/-- A pre-sampled candidate's cap-stopped population is included in the
selected reserve-spine BRW population at its fixed endpoint. The split
generation is read from the reserve spine; the candidate subtree follows the
first selected child, while the spine follows the second.
-/
theorem selectedReserveSpineCandidate_subset_restartBRWPopulation_at_endpoint
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r k ω)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) :
    rootedCapStoppedPopulation growth cap ω
        ((selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
          R r PUnit.unit (k + 1) ω) duration ⊆
      selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r
        (k + 1 + duration) ω := by
  let candidateRoot :=
    (selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
      R r PUnit.unit (k + 1) ω
  have henabled : k ∈ selectedReserveSpineCandidateEnabled R r duration
      (k + 1 + duration) ω := by
    simp [selectedReserveSpineCandidateEnabled, halive, hsplit]
    omega
  intro q hq
  have hcandidate : q ∈ selectedReserveSpineCandidatePopulation R growth hR
      cap duration r (k + 1 + duration) ω := by
    apply (mem_selectedReserveSpineCandidatePopulation_iff R growth hR
      cap duration r (k + 1 + duration) ω q).2
    refine ⟨k, henabled, ?_⟩
    simpa [candidateRoot, RootIndexed.ReserveLineages.capStoppedCandidate,
      Nat.add_sub_cancel_left] using hq
  exact Finset.mem_union_right _ hcandidate

/-- A successful pre-sampled candidate contributes at least its lower
population bound to the selected reserve-spine BRW population at its fixed
endpoint. The candidate subtree follows the first selected child, while the
spine follows the second.
-/
theorem selectedReserveSpineRestartBRWPopulation_card_ge_of_candidate_success
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (lower upper duration : ℕ) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r k ω)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R)
    (hupper : 1 ≤ upper)
    (hsuccess : growthTrialSuccess growth lower upper duration
      (fun v =>
        let q := (selectedReserveSpineLineages (Root := Root) R hR).firstChildRootAt
          R r PUnit.unit (k + 1) ω
        ω q.1 (q.2 ++ v))) :
    lower ≤ (selectedReserveSpineRestartBRWPopulationSlice R growth hR upper duration
      r (k + 1 + duration) ω).card := by
  let lineages := selectedReserveSpineLineages (Root := Root) R hR
  let candidateRoot := lineages.firstChildRootAt R r PUnit.unit (k + 1) ω
  have hcandidate := rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess
    growth lower upper duration ω candidateRoot hupper (by simpa [candidateRoot] using hsuccess)
  have hcapStoppedCandidate_subset_selectedReserveSpineBRWPopulation : rootedCapStoppedPopulation growth upper ω candidateRoot duration ⊆
      selectedReserveSpineRestartBRWPopulationSlice R growth hR upper duration r
        (k + 1 + duration) ω := by
    simpa [candidateRoot] using
      selectedReserveSpineCandidate_subset_restartBRWPopulation_at_endpoint
        R growth hR upper duration r k ω halive hsplit
  have hcard := Finset.card_le_card hcapStoppedCandidate_subset_selectedReserveSpineBRWPopulation
  omega

/-- The causal reserve-spine BRW population made from the reserve singleton
and all generation-enabled cap-stopped first-child trials.  Candidate windows
are defined on the common pre-sampled field before any success outcomes are
examined. -/
noncomputable def selectedReserveSpineRestartBRWPopulation
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α X) Root α X
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) id where
  toPopulation ω := {
    particles := fun n =>
      ↑(selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r n ω)
    depth := by
      intro n q hq
      rw [selectedReserveSpineRestartBRWPopulationSlice, Finset.mem_coe,
        Finset.mem_union] at hq
      rcases hq with hspine | hcandidate
      · by_cases ha : selectedReserveSpineAlive R r n ω
        · simp only [ha, ite_true, Finset.mem_singleton] at hspine
          subst q
          exact selectedReserveSpinePath_depth R r ω n
        · simp [ha] at hspine
      · exact selectedReserveSpineCandidate_node_depth R growth hR cap
          duration r n ω q hcandidate
    successor := by
      intro n q hq
      rw [selectedReserveSpineRestartBRWPopulationSlice, Finset.mem_coe,
        Finset.mem_union] at hq
      rcases hq with hspine | hcandidate
      · have hactive := hspine
        by_cases ha : selectedReserveSpineAlive R r (n + 1) ω
        · have hactive' : selectedReserveSpineAlive R r n ω ∧
              (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty := by
            simpa only [selectedReserveSpineAlive] using ha
          have hq' : q = (r, selectedReserveSpinePath R r (n + 1) ω) := by
            simpa [selectedReserveSpineRestartBRWPopulationSlice, ha] using hspine
          subst q
          have hedge := selectedReserveSpinePath_succ_selected_of_nonempty
            R r n ω hactive'.2
          have hp : (r, selectedReserveSpinePath R r n ω) ∈
              selectedReserveSpineRestartBRWPopulationSlice R growth hR
                cap duration r n ω := by
            simp [selectedReserveSpineRestartBRWPopulationSlice, hactive'.1]
          apply Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          refine ⟨(r, selectedReserveSpinePath R r n ω), hp,
            reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω)),
            R.subset_support _ _ hedge.2, ?_⟩
          simpa [Combinatorics.UlamHarris.RootIndexed.childAddress] using
            congrArg (fun p : TreeNode α => (r, p)) hedge.1
        · simp [ha] at hspine
      · obtain ⟨k, hk, hcandidate⟩ :=
          (mem_selectedReserveSpineCandidatePopulation_iff R growth hR
            cap duration r (n + 1) ω q).mp hcandidate
        have hk_le : k ≤ n := by
          have hk_range : k < n + 1 := by
            change k ∈ (Finset.range (n + 1)).filter _ at hk
            exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
          omega
        by_cases hnew : k = n
        · subst k
          have hsplit :
              ω r (selectedReserveSpinePath R r n ω) ∈ splitBy R := by
            change n ∈ (Finset.range (n + 1)).filter _ at hk
            exact (Finset.mem_filter.mp hk).2.2.1
          have hqroot : q =
              (selectedReserveSpineLineages R hR).firstChildRootAt
                R r PUnit.unit (n + 1) ω := by
            have hzero :=
              (selectedReserveSpineLineages R hR).capStoppedCandidate_zero
                R growth cap r PUnit.unit (n + 1) ω
            have hcandidate0 : q ∈
                (selectedReserveSpineLineages R hR).capStoppedCandidate
                  R growth cap r PUnit.unit (n + 1) 0 ω := by
              simpa using hcandidate
            rw [hzero] at hcandidate0
            exact Finset.mem_singleton.mp hcandidate0
          rw [hqroot]
          have hroot := selectedReserveSpineCandidate_root_at_split
            R hR r n ω hsplit
          have hroot' := hroot.2
          let slot := firstSelectedSlot R
            (ω r (selectedReserveSpinePath R r n ω))
          let parent := (r, selectedReserveSpinePath R r n ω)
          have hparent : parent ∈
              selectedReserveSpineRestartBRWPopulationSlice R growth hR
                cap duration r n ω := by
            have hk_parts := Finset.mem_filter.mp hk
            have halive : selectedReserveSpineAlive R r n ω := hk_parts.2.1
            simp [parent, selectedReserveSpineRestartBRWPopulationSlice, halive]
          apply Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          refine ⟨parent, hparent, slot, R.subset_support _ _ hroot', ?_⟩
          simp [parent, slot, hroot.1,
            Combinatorics.UlamHarris.RootIndexed.childAddress]
        · have hprevEnabled : k ∈
              selectedReserveSpineCandidateEnabled R r duration n ω := by
            have hk_parts := Finset.mem_filter.mp hk
            have hk_range : k < n := by omega
            change k ∈ (Finset.range n).filter _
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_range.mpr hk_range, ?_⟩
            refine ⟨hk_parts.2.1, hk_parts.2.2.1, ?_⟩
            omega
          have hage : n + 1 - (k + 1) = n - (k + 1) + 1 := by omega
          have hparent : q ∈
              rootedCapStoppedPopulation growth cap ω
                ((selectedReserveSpineLineages R hR).firstChildRootAt
                  R r PUnit.unit (k + 1) ω)
                (n - (k + 1) + 1) := by
            simpa [RootIndexed.ReserveLineages.capStoppedCandidate,
              hage] using hcandidate
          have hsucc :=
            (rootedCapStoppedPopulation_succ_subset growth cap
              (n - (k + 1)) ω
              ((selectedReserveSpineLineages R hR).firstChildRootAt
                R r PUnit.unit (k + 1) ω)) hparent
          rcases Combinatorics.Branching.Population.mem_offspringAddressSet.mp
              hsucc with ⟨p, hp, i, hi, hchild⟩
          have hselectedBRWParent : p ∈
              selectedReserveSpineRestartBRWPopulationSlice R growth hR
                cap duration r n ω := by
            apply Finset.mem_coe.mpr
            apply Finset.mem_union_right
            apply (mem_selectedReserveSpineCandidatePopulation_iff R growth hR
              cap duration r n ω p).mpr
            have hpFin : p ∈ rootedCapStoppedPopulation growth cap ω
                ((selectedReserveSpineLineages R hR).firstChildRootAt
                  R r PUnit.unit (k + 1) ω) (n - (k + 1)) :=
              Finset.mem_coe.mp hp
            exact ⟨k, hprevEnabled, by
              simpa [RootIndexed.ReserveLineages.capStoppedCandidate] using hpFin⟩
          apply Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          refine ⟨p, hselectedBRWParent, i, ?_, hchild⟩
          exact growth.subset_support (ω p.1 p.2) i hi
  }
  adapted := by
    intro p n
    have hreserve : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        (fun ω => if selectedReserveSpineAlive R r n ω then
          ({(r, selectedReserveSpinePath R r n ω)} :
            Finset (RootIndexed.TreeNode Root α)) else ∅) := by
      apply (@measurable_finset_iff (RootIndexed.TreeNode Root α)
        (RootIndexed.StepField Root α X)
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) n)).2
      intro q
      have hspine : Measurable[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) n]
          (fun ω => q ∈ selectedReserveSpineSlice R r n ω) := by
        simpa [selectedReserveSpinePopulation] using
          (selectedReserveSpinePopulation R hR r).adapted q n
      convert hspine using 1
      ext ω
      by_cases ha : selectedReserveSpineAlive R r n ω
      · simp [ha, selectedReserveSpineSlice]
      · simp [ha, selectedReserveSpineSlice]
    have hcandidates := selectedReserveSpineCandidatePopulation_adapted
      R growth hR hgrowth cap duration r n
    have hselectedBRWPopulationSliceMeasurable : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        (fun ω => selectedReserveSpineRestartBRWPopulationSlice R growth hR
          cap duration r n ω) := by
      have hunion : Measurable (fun ab :
          Finset (RootIndexed.TreeNode Root α) ×
            Finset (RootIndexed.TreeNode Root α) => ab.1 ∪ ab.2) := by
        apply (@measurable_finset_iff (RootIndexed.TreeNode Root α)
          (Finset (RootIndexed.TreeNode Root α) ×
            Finset (RootIndexed.TreeNode Root α)) inferInstance).2
        intro q
        simpa only [Finset.mem_union, Function.comp_apply] using
          (((measurable_finset_mem q).comp measurable_fst).or
            ((measurable_finset_mem q).comp measurable_snd))
      change Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        (fun ω => (if selectedReserveSpineAlive R r n ω then
          ({(r, selectedReserveSpinePath R r n ω)} :
            Finset (RootIndexed.TreeNode Root α)) else ∅) ∪
          selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω)
      exact hunion.comp (hreserve.prodMk hcandidates)
    exact (measurable_finset_mem p).comp hselectedBRWPopulationSliceMeasurable

/-- The causal reserve-spine BRW population has finite slices: each slice is represented
by the finite union in `selectedReserveSpineRestartBRWPopulationSlice`. -/
theorem selectedReserveSpineRestartBRWPopulation_finiteSlices
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ) (r : Root) :
    (selectedReserveSpineRestartBRWPopulation R growth hR hgrowth cap duration r).FiniteSlices := by
  intro n ω
  change (↑(selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r n ω) :
    Set (RootIndexed.TreeNode Root α)).Finite
  exact (selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r n ω).finite_toSet

/-- Deterministic cardinal bound for the finite presentation of the causal
reserve-spine BRW population. It counts every still-open fixed candidate window; it makes
no assumption on trial outcomes or on nonempty offspring. -/
theorem selectedReserveSpineRestartBRWPopulation_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (cap duration : ℕ)
    (hbounded : growth.IsBoundedBy 2) (hcap : 1 ≤ cap) (r : Root)
    (hfinite :
      (selectedReserveSpineRestartBRWPopulation R growth hR hgrowth cap duration r).FiniteSlices)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    (hfinite.toFinset n ω).card ≤ 1 + (duration + 1) * (2 * cap) := by
  have heq : hfinite.toFinset n ω =
      selectedReserveSpineRestartBRWPopulationSlice R growth hR cap duration r n ω := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  rw [heq]
  change ((if selectedReserveSpineAlive R r n ω then
      ({(r, selectedReserveSpinePath R r n ω)} : Finset
        (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤ _
  exact selectedReserveSpineAndCandidates_card_le R growth hR cap duration
    hbounded hcap r n ω

end ProbabilityTheory.BranchingRandomWalk

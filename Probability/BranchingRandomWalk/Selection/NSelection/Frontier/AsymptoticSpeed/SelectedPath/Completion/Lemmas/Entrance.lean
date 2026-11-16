/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialPosition
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.Population
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition
import Mathlib.Data.Fintype.EquivFin
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Lemmas.PositivePart

/-!
# Displacement within a bounded growth trial

## Internal proof declarations

* `trialResetPositionAtGeneration` is the maximum position of the terminal
  candidate born at $n-d$, evaluated at completion generation $n$.
* `trialResetPositionAtGeneration_measurable`: that maximum is observable at $n$.
* `trialResetPositionAtGeneration_le` bounds it by the growth-root position
  plus $Md$ when all retained edges cost at most $M$.
* `entrance_count_le_at_trialResetPosition_ae`: if the trial succeeds with at
  least $m$ particles then at least $m$ actual selected particles lie at or
  below its maximum.

* `trialRestartPopulationBeforeReset` gives the selected-path particle before
  the successful trial is born, and the descendants in that trial between its
  birth and its completion $\tau$.
* `trialRestart_beforeReset_and_shift_le`: for generation $H$, the positive
  positions before the reset and the positive reset location on $\{\tau\le H\}$
  are bounded by $MH+\sum_{j<H}(Y_j)_+$.
* `trialRestartPopulationBeforeReset_positionWitness_ae`: up to $\tau$,
  each particle at position $x$ has an actual selected counterpart at the
  same generation at position at most $x$, when the selected path is alive.

* `growthTrial_position_le_cutoff_add_selectedMarkSum` bounds the positive
  position at age $j$ of a trial born at $k+1$ by $M(k+1+j)+\sum_{i<k}(Y_i)_+$.
* `firstSuccessfulTrial_positionWitness_during_window_ae`: from the birth
  of the successful growth trial through completion, each member $u$ has
  an actual selected counterpart $v$ at the same generation with $X(v)\le X(u)$.
* `rootedCapStoppedPopulation_pathPotential_le`: if every edge selected by a
  growth trial has potential at most $M$, a particle $v$ at trial age $d$
  satisfies $V(v) \le V(u)+Md$, where $u$ is the trial root.
* `entrance_count_le_of_trial_success_ae`: a successful trial rooted at $u$
  with $V(u) \le x$ gives at least $m$ distinct particles of the $N$-selection
  population with position at most $x+Md$.
* `entrance_count_le_at_firstSuccessfulCompletion_ae`: the same entrance
  count bound holds at the finite first successful completion $\tau$.
* `position_endpointNodesByRank_le_of_entrance_count`: once the actual population
  at $\tau$ contains at least $m$ particles at positions at most $x$, all $m$
  endpoint coordinates selected for the continuation are at positions at most $x$.
* `firstSuccess_rankedEntrance_le_ae`: the $m$ ranked roots at $\tau$ have
  positions at most $V(v_\kappa)+Md$, with $v_\kappa$ indexed by trial order.

* `measure_badEntrance_le`: the probability of missing entrance by $T$
  with $m$ actual particles at or below $c$ is bounded by the probability
  of missing the first-$K$ completion deadline plus the trial-root tail.

This is the bounded-growth contribution to the entrance estimate in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.Branching.Step.FiniteSelection
open SelectedPath.GrowthTrial
open SelectedPath.GrowthTrial.Lemmas
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate)
open GrowthTrial.Population (capStoppedCandidate capStoppedPopulation capStoppedPopulation_succ_parent
  rootedCapStoppedPopulation rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess
  rootedCapStoppedPopulation_node_depth capStoppedCandidate_adapted)


private lemma capStoppedPopulation_pathPotential_le
    {α X : Type*} [MeasurableSpace X] (growth : Step.FiniteSelection α X)
    (φ : Potential X) (M : ℝ)
    (hbound : ∀ ξ i, i ∈ growth ξ → ξ.potentialValue' φ i ≤ M)
    (cap age : ℕ) (ω : Mark α (Step α X)) (v : TreeNode α)
    (hv : v ∈ capStoppedPopulation growth cap age ω) :
    Spine.pathPotential φ ω v ≤ M * age := by
  induction age generalizing v with
  | zero =>
    have hv0 : v = [] := by simpa using hv
    subst v
    simp [Spine.pathPotential]
  | succ age ih =>
    obtain ⟨u, hu, i, hi, rfl⟩ := capStoppedPopulation_succ_parent growth cap age ω v hv
    rw [Spine.pathPotential_append, Spine.pathPotential_singleton,
      ProbabilityTheory.BranchingRandomWalk.subtreeStepField, List.append_nil, Nat.cast_succ]
    linarith [ih u hu, hbound (ω u) i hi]

lemma rootedCapStoppedPopulation_pathPotential_le
    {Root α X : Type*} [MeasurableSpace X] (growth : Step.FiniteSelection α X)
    (φ : Potential X) (M : ℝ)
    (hbound : ∀ ξ i, i ∈ growth ξ → ξ.potentialValue' φ i ≤ M)
    (cap age : ℕ) (ω : RootIndexed.StepField Root α X)
    (u v : RootIndexed.TreeNode Root α)
    (hv : v ∈ rootedCapStoppedPopulation growth cap ω u age) :
    Spine.pathPotential φ (ω v.1) v.2 ≤ Spine.pathPotential φ (ω u.1) u.2 + M * age := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
  change Spine.pathPotential φ (ω u.1) (u.2 ++ w) ≤ _
  rw [Spine.pathPotential_append]
  exact add_le_add le_rfl (capStoppedPopulation_pathPotential_le growth φ M hbound cap age
    (ProbabilityTheory.BranchingRandomWalk.subtreeStepField u.2 (ω u.1)) w hw)

private lemma entrance_count_le_of_trial_positions_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection α ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (r : Root) (k : ℕ) :
    let n := k + 1 + duration
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let population := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
      id trials.toFinset n
    let selectedField := RootIndexed.restartedRealPositionNSelectedBRWField N {r} (fun _ => 0)
      id trials.toFinset n
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) left
      left ∈ successEvent R growth hR lower upper duration r k →
      ∀ x : ℝ, (∀ q ∈ rootedCapStoppedPopulation growth upper left u duration,
        RootIndexed.position (fun _ => 0) id left q.1 q.2 ≤ x) →
        lower ≤ ((population field).filter fun p =>
          RootIndexed.position (fun _ => 0) id (selectedField field) p.1 p.2 ≤
            x).card := by
  classical
  dsimp only
  let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
    upper duration r
  have hcoupling := Coupling.selectedToNSelectedBRWInjection_ae
    μ hnorm N (fun _ => 0) R growth hR hgrowth upper duration hbounded hupper
    hcapacity r (k + 1 + duration)
  filter_upwards [hcoupling] with field ⟨dom⟩
  intro hsuccess x hx
  let left := RootIndexed.StepField.left field
  let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) left
  let endpoints := rootedCapStoppedPopulation growth upper left u duration
  obtain ⟨halive, hsplit, htrial⟩ := hsuccess
  have htrial' : growthTrialSuccess growth lower upper duration
      (fun v => left u.1 (u.2 ++ v)) := htrial
  have hcount : lower ≤ endpoints.card :=
    rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess
      growth lower upper duration left u hupper htrial'
  have hmem {q : RootIndexed.TreeNode Root α} (hq : q ∈ endpoints) :
      q ∈ trials.toFinset (k + 1 + duration) field := by
    have hslice : trials.toFinset (k + 1 + duration) field =
        SelectedPath.Population.slice R growth hR upper duration r (k + 1 + duration) left := by
      apply Finset.coe_injective
      rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
      simp [left, SelectedPath.Population.leftBRWFamily,
        RootIndexed.CausalPopulation.pullback_population, SelectedPath.Population.family]
      congr!
    rw [hslice]
    exact SelectedPath.Population.growthTrial_subset_at_endpoint R growth hR upper
      duration r k left halive hsplit hq
  refine hcount.trans (Finset.card_le_card_of_injOn dom ?_ ?_)
  · intro q hq
    have hq' : q ∈ endpoints := hq
    have hparticle := hmem hq'
    apply Finset.mem_filter.mpr
    refine ⟨dom.mapsTo hparticle, ?_⟩
    have hdom := dom.dominates q hparticle
    exact hdom.trans (hx q hq')
  · exact dom.injOn.mono fun _ hq => hmem hq

lemma entrance_count_le_of_trial_success_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection α ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (M : ℝ) (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (r : Root) (k : ℕ) :
    let n := k + 1 + duration
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let population := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
      id trials.toFinset n
    let selectedField := RootIndexed.restartedRealPositionNSelectedBRWField N {r} (fun _ => 0)
      id trials.toFinset n
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) left
      left ∈ successEvent R growth hR lower upper duration r k →
      ∀ x : ℝ, Spine.pathPotential realPotential (left u.1) u.2 ≤ x →
        lower ≤ ((population field).filter fun p =>
          RootIndexed.position (fun _ => 0) id (selectedField field) p.1 p.2 ≤
            x + M * duration).card := by
  dsimp only
  have hcount := entrance_count_le_of_trial_positions_ae μ hnorm N R growth hR hgrowth
    lower upper duration hupper hbounded hcapacity r k
  filter_upwards [hcount] with field hf hsuccess x hx
  apply hf hsuccess (x + M * duration)
  intro q hq
  have hpos := rootedCapStoppedPopulation_pathPotential_le growth realPotential M hcutoff
    upper duration (RootIndexed.StepField.left field) _ q hq
  have hs : RootIndexed.position (fun _ => 0) id (RootIndexed.StepField.left field) q.1 q.2 =
      Spine.pathPotential realPotential ((RootIndexed.StepField.left field) q.1) q.2 := by
    simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential, realPotential]
  rw [hs]
  exact hpos.trans (add_le_add_left hx _)

/-- The terminal growth-trial maximum at generation `n`.
The zero value on an empty candidate totalizes the observable. -/
noncomputable def trialResetPositionAtGeneration
    {Root : Type*} (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (upper duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root ℕ ℝ) : ℝ :=
  let S := capStoppedCandidate (lineages R hR) R growth upper r
    PUnit.unit (n - duration) duration ω
  if hS : S.Nonempty then S.sup' hS (fun q =>
    RootIndexed.positionAtGeneration (fun _ => 0) id n q.1 q.2 ω)
  else 0

lemma trialResetPositionAtGeneration_measurable
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [Countable (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (upper duration : ℕ) (r : Root) (n : ℕ) (hn : duration ≤ n) :
    Measurable[RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ) n]
      (trialResetPositionAtGeneration R growth hR upper duration r n) := by
  classical
  let Ω := RootIndexed.StepField Root ℕ ℝ
  let F := RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ) n
  let S := capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit
    (n - duration) duration
  have hS := capStoppedCandidate_adapted (lineages R hR) R growth hR hgrowth upper r
    PUnit.unit (n - duration) duration
  rw [Nat.sub_add_cancel hn] at hS
  let f (s : Finset (RootIndexed.TreeNode Root ℕ)) (ω : Ω) : ℝ :=
    if hs : s.Nonempty then s.sup' hs (fun q =>
      RootIndexed.positionAtGeneration (fun _ => 0) id n q.1 q.2 ω)
    else 0
  have hf (s : Finset (RootIndexed.TreeNode Root ℕ)) : Measurable[F] (f s) := by
    by_cases hs : s.Nonempty
    · let _ : MeasurableSpace Ω := F
      have h := Finset.measurable_sup' (δ := Ω) hs (f := fun q =>
        RootIndexed.positionAtGeneration (fun _ => 0) id n q.1 q.2)
        (fun q _ => RootIndexed.positionAtGeneration_measurable _ id measurable_id n q.1 q.2)
      simp only [f, dite_eq_left hs]
      convert h using 1
      funext ω
      simp only [Finset.sup'_apply]
    · simpa only [f, dite_eq_right hs] using (measurable_const (a := (0 : ℝ)))
  intro B hB
  change MeasurableSet[F] ((fun ω => f (S ω) ω) ⁻¹' B)
  have heq : (fun ω => f (S ω) ω) ⁻¹' B =
      ⋃ s : Finset (RootIndexed.TreeNode Root ℕ), S ⁻¹' {s} ∩ f s ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨S ω, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩
  rw [heq]
  exact MeasurableSet.iUnion fun s => (hS (measurableSet_singleton s)).inter (hf s hB)

/-- The reset position is at most the growth-root position plus the
cutoff times the number of growth generations. -/
lemma trialResetPositionAtGeneration_le
    {Root : Type*} (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (lower upper duration : ℕ) (r : Root) (k : ℕ)
    (hupper : 1 ≤ upper) (hlower : 0 < lower)
    (M : ℝ) (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (ω : RootIndexed.StepField Root ℕ ℝ)
    (hs : ω ∈ successEvent R growth hR lower upper duration r k) :
    let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) ω
    trialResetPositionAtGeneration R growth hR upper duration r (k + 1 + duration) ω ≤
      Spine.pathPotential realPotential (ω u.1) u.2 + M * duration := by
  intro u
  let S := rootedCapStoppedPopulation growth upper ω u duration
  have hcard : lower ≤ S.card :=
    rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess growth lower upper duration ω
      u hupper hs.2.2
  have hne : S.Nonempty := Finset.card_pos.mp (hlower.trans_le hcard)
  have hu : u.2.length = k + 1 := growthTrialRootAt_depth (lineages R hR) R r
    PUnit.unit (k + 1) ω
  have hc : trialResetPositionAtGeneration R growth hR upper duration r (k + 1 + duration) ω =
      S.sup' hne (fun q =>
        RootIndexed.positionAtGeneration (fun _ => 0) id (k + 1 + duration) q.1 q.2 ω) := by
    simp only [trialResetPositionAtGeneration, Nat.add_sub_cancel, dite_eq_left hne, S, u,
      capStoppedCandidate]
  rw [hc, Finset.sup'_le_iff]
  intro q hq
  have hdepth := rootedCapStoppedPopulation_node_depth growth upper ω u q duration hq
  rw [RootIndexed.positionAtGeneration, ite_eq_left (hdepth.trans (congrArg (· + duration) hu))]
  have hpos : RootIndexed.position (fun _ => 0) id ω q.1 q.2 =
      Spine.pathPotential realPotential (ω q.1) q.2 := by
    simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential, realPotential]
  rw [hpos]
  exact rootedCapStoppedPopulation_pathPotential_le growth realPotential M hcutoff
    upper duration ω u q hq

lemma entrance_count_le_at_trialResetPosition_ae
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) (k : ℕ) :
    let n := k + 1 + duration
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let population := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
      id trials.toFinset n
    let selectedField := RootIndexed.restartedRealPositionNSelectedBRWField N {r} (fun _ => 0)
      id trials.toFinset n
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      left ∈ successEvent R growth hR lower upper duration r k →
      lower ≤ ((population field).filter fun q =>
        RootIndexed.position (fun _ => 0) id (selectedField field) q.1 q.2 ≤
          trialResetPositionAtGeneration R growth hR upper duration r n left).card := by
  dsimp only
  have hcount := entrance_count_le_of_trial_positions_ae μ hnorm N R growth hR hgrowth
    lower upper duration hupper hbounded hcapacity r k
  filter_upwards [hcount] with field hf hs
  apply hf hs
  intro q hq
  let ω := RootIndexed.StepField.left field
  let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) ω
  let S := rootedCapStoppedPopulation growth upper ω u duration
  have hqS : q ∈ S := hq
  have hdepth := rootedCapStoppedPopulation_node_depth growth upper ω u q duration hqS
  have hu : u.2.length = k + 1 := growthTrialRootAt_depth (lineages R hR) R r
    PUnit.unit (k + 1) ω
  have hne : S.Nonempty := ⟨q, hqS⟩
  have hc : trialResetPositionAtGeneration R growth hR upper duration r (k + 1 + duration) ω =
      S.sup' hne (fun q =>
        RootIndexed.positionAtGeneration (fun _ => 0) id (k + 1 + duration) q.1 q.2 ω) := by
    simp only [trialResetPositionAtGeneration, Nat.add_sub_cancel, dite_eq_left hne, S, u,
      capStoppedCandidate]
  change RootIndexed.position (fun _ => 0) id ω q.1 q.2 ≤
    trialResetPositionAtGeneration R growth hR upper duration r (k + 1 + duration) ω
  rw [hc]
  have hle := Finset.le_sup' (fun q =>
    RootIndexed.positionAtGeneration (fun _ => 0) id (k + 1 + duration) q.1 q.2 ω) hqS
  simpa only [RootIndexed.positionAtGeneration, hdepth.trans (congrArg (· + duration) hu),
    ite_true] using hle


lemma entrance_count_le_at_firstSuccessfulCompletion_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection α ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (M : ℝ) (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (r : Root) :
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let population (n : ℕ) := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
      (fun _ => 0) id trials.toFinset n
    let selectedField (n : ℕ) := RootIndexed.restartedRealPositionNSelectedBRWField N {r}
      (fun _ => 0) id trials.toFinset n
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      ∀ n : ℕ, firstSuccessfulCompletion R growth hR lower upper duration r left = n →
        ∃ k : ℕ, k + 1 + duration = n ∧
          left ∈ successEvent R growth hR lower upper duration r k ∧
          let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) left
          lower ≤ ((population n field).filter fun p =>
            RootIndexed.position (fun _ => 0) id (selectedField n field) p.1 p.2 ≤
              Spine.pathPotential realPotential (left u.1) u.2 + M * duration).card := by
  classical
  dsimp only
  have hentrance (k : ℕ) := entrance_count_le_of_trial_success_ae
    μ hnorm N R growth hR hgrowth lower upper duration hupper hbounded hcapacity M hcutoff r k
  filter_upwards [ae_all_iff.2 hentrance] with field hfield
  intro n hn
  let left := RootIndexed.StepField.left field
  let declarations : ℕ → Set (RootIndexed.StepField Root α ℝ) := fun i =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = i ∧
      ω ∈ successEvent R growth hR lower upper duration r k}
  have hfirst : firstDeclaredSuccess declarations left = (n : WithTop ℕ) := hn
  obtain ⟨k, hk, hsuccess⟩ := ((firstDeclaredSuccess_eq_iff declarations left n).mp hfirst).1
  have htime : k + 1 + duration = n := WithTop.coe_injective hk
  subst n
  exact ⟨k, rfl, hsuccess, hfield k hsuccess _ le_rfl⟩

lemma position_endpointNodesByRank_le_of_entrance_count
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (R growth : Step.FiniteSelection α ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Completion.time R growth hR hgrowth lower upper duration r field = n)
    (x : ℝ) :
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let population := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
      id trials.toFinset n field
    let selectedField := RootIndexed.restartedRealPositionNSelectedBRWField N {r}
      (fun _ => 0) id trials.toFinset n field
    lower ≤ (population.filter fun p => RootIndexed.position (fun _ => 0)
      id selectedField p.1 p.2 ≤ x).card →
    ∀ i : Fin lower,
      let p := Completion.endpointNodesByRank N (fun _ => 0) R growth hR hgrowth
        lower upper duration r field i
      RootIndexed.position (fun _ => 0) id selectedField p.1 p.2 ≤ x := by
  classical
  let : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  dsimp only
  intro hcount i
  let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
    upper duration r
  let population := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
    id trials.toFinset
  let selectedField := RootIndexed.restartedRealPositionNSelectedBRWField N {r}
    (fun _ => 0) id trials.toFinset
  let position (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) :=
    RootIndexed.observedPositionAtGeneration (fun _ => 0) id id n (selectedField n field) p
  let τ := Completion.time R growth hR hgrowth lower upper duration r
  let p := Completion.endpointNodesByRank N (fun _ => 0) R growth hR hgrowth
    lower upper duration r field i
  have hcard : lower ≤ (population n field).card := by
    refine hcount.trans (Finset.card_le_card ?_)
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hp : p ∈ population n field :=
    particleRankVectorAtStoppingTime_mem τ position population lower (r, []) field n htime hcard i
  have hrank : rankBy (position n field) (population n field) p = i.val :=
    particleRankVectorAtStoppingTime_rank τ position population lower (r, []) field n htime hcard i
  have hpos_eq {q : RootIndexed.TreeNode Root α} (hq : q ∈ population n field) :
      position n field q =
        RootIndexed.position (fun _ => 0) id (selectedField n field) q.1 q.2 := by
    exact RootIndexed.observedPositionAtGeneration_eq (fun _ => 0) id id n
      (selectedField n field) q
      (RootIndexed.selectedPopulationTotalized_depth N {r} (fun _ => 0)
        id id n (selectedField n field) q hq)
  change RootIndexed.position (fun _ => 0) id (selectedField n field) p.1 p.2 ≤ x
  rw [← hpos_eq hp]
  by_contra! hpx
  have hsub : ((population n field).filter fun q =>
        RootIndexed.position (fun _ => 0) id (selectedField n field) q.1 q.2 ≤ x) ⊆
      (population n field).filter fun q => valueKey (position n field) q <
        valueKey (position n field) p := by
    intro q hq
    obtain ⟨hqmem, hqpos⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hqmem, valueKey_lt_of_value_lt (position n field)
      ((hpos_eq hqmem).trans_le hqpos |>.trans_lt hpx)⟩
  have hle : lower ≤ rankBy (position n field) (population n field) p := by
    rw [rankBy_eq_card_filter]
    exact hcount.trans (Finset.card_le_card hsub)
  exact (i.isLt.not_ge (hrank ▸ hle))

lemma firstSuccess_rankedEntrance_le_ae
    {Root : Type} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (M : ℝ) (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (r : Root) :
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let selectedField (n : ℕ) := RootIndexed.restartedRealPositionNSelectedBRWField N {r}
      (fun _ => 0) id trials.toFinset n
    let G := growthTrialSuccess growth lower upper duration
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      (∀ u, (R (left r u)).Nonempty) →
      ∀ t : ℕ, Completion.time R growth hR hgrowth lower upper duration r field = t →
        ∃ k : ℕ, (splitCycle R (splitWaitingDisplacement R) G k (left r)).2 ∧
          (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j (left r)).2) ∧
          ∀ i : Fin lower,
            let p := Completion.endpointNodesByRank N (fun _ => 0) R growth hR hgrowth
              lower upper duration r field i
            RootIndexed.position (fun _ => 0) id (selectedField t field) p.1 p.2 ≤
              Spine.pathPotential realPotential (left r) (trialGrowthRoot R k (left r)) +
                M * duration := by
  have hentrance := entrance_count_le_at_firstSuccessfulCompletion_ae μ hnorm N R growth hR
    hgrowth lower upper duration hupper hbounded hcapacity M hcutoff r
  filter_upwards [hentrance] with field henter
  dsimp only
  let left := RootIndexed.StepField.left field
  intro hne t ht
  have ht' : firstSuccessfulCompletion R growth hR lower upper duration r left = t := ht
  obtain ⟨n, hn, _, hsuccess, hbefore, hroot⟩ :=
    splitCycle_first_success_at_completion R growth hR lower upper duration r left hne t ht'
  obtain ⟨j, hj, _, hcount⟩ := henter t ht'
  have hnj : j = n := by omega
  subst j
  let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (n + 1) left
  have hu : u.1 = r := growthTrialRootAt_root (lineages R hR) R r PUnit.unit (n + 1) left
  change trialGrowthRoot R (splitCount R r n left) (left r) = u.2 at hroot
  refine ⟨splitCount R r n left, hsuccess, hbefore, ?_⟩
  rw [hroot, ← hu]
  exact position_endpointNodesByRank_le_of_entrance_count N R growth hR hgrowth
    lower upper duration r field t ht _ hcount

/-- Combine the clock, first successful trial index, and position estimates
for the entrance of the single-root process. -/
lemma measure_badEntrance_le
    {Root : Type} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (hRne : μ {ξ | (R ξ).Nonempty} = 1)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (M : ℝ) (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (r : Root) (T K : ℕ) (x c : ℝ)
    (hc : x + (K : ℝ) * M + M * duration ≤ c) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N {r}
      (fun _ => 0) id trials.toFinset
    let Pop := RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
      (fun _ => 0) id trials.toFinset
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let G := growthTrialSuccess growth lower upper duration
    let large := {ω | ∃ k < K, (splitCycle R (splitWaitingDisplacement R) G k ω).2 ∧
      (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j ω).2) ∧
      (x + ((K - 1 : ℕ) : ℝ) * M ≤
        Spine.pathPotential realPotential ω (trialSplitParent R k ω) ∨
       x + (K : ℝ) * M ≤ Spine.pathPotential realPotential ω (trialGrowthRoot R k ω))}
    let E := {field | splitCount R r ((τ field).untopD 0 - (duration + 1))
        (RootIndexed.StepField.left field) < K} ∩ {field | τ field ≤ (T : WithTop ℕ)}
    P {field | ¬ ∃ i ≤ T, (∃ e : Fin lower ↪ RootIndexed.TreeNode Root ℕ,
      ∀ j, e j ∈ Pop i field ∧
        RootIndexed.position (fun _ => 0) id (stage i field) (e j).1 (e j).2 ≤ c) ∧
        τ field = i} ≤
      P Eᶜ + offspringFieldLaw μ large := by
  intro τ trials stage Pop P G large E
  let left : RootIndexed.StepField (Root ⊕ Root) ℕ ℝ → RootIndexed.StepField Root ℕ ℝ :=
    RootIndexed.StepField.left
  let f := fun field => left field r
  let Q := RootIndexed.stepFieldLaw (Root := Root) μ
  let ν := offspringFieldLaw μ
  have hleft : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
  have hleftlaw : P.map left = Q := RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective
  have hf : Measurable f := (measurable_pi_apply r).comp hleft
  have hflaw : P.map f = ν := by
    change P.map ((fun ω : RootIndexed.StepField Root ℕ ℝ => ω r) ∘ left) = ν
    rw [← Measure.map_map (measurable_pi_apply r) hleft, hleftlaw,
      RootIndexed.stepFieldLaw_root_marginal μ r]
  have hlarge : P (f ⁻¹' large) ≤ ν large :=
    (Measure.le_map_apply hf.aemeasurable large).trans_eq (congrArg (fun m => m large) hflaw)
  have hRneMeas : MeasurableSet {ξ | (R ξ).Nonempty} := by
    have hm : Measurable (fun ξ => (R ξ).card) :=
      (measurable_of_countable fun s : Finset ℕ => s.card).comp hR
    rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
      ext ξ
      exact Finset.card_pos.symm]
    exact hm measurableSet_Ioi
  have hall : ∀ᵐ field ∂P, ∀ u, (R (f field u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have hmeas : Measurable (fun field => f field u) := (measurable_pi_apply u).comp hf
    have hlaw : P.map (fun field => f field u) = μ := by
      change P.map ((fun ω : Mark ℕ (Step ℕ ℝ) => ω u) ∘ f) = μ
      rw [← Measure.map_map (measurable_pi_apply u) hf, hflaw, offspringFieldLaw_coordinate μ u]
    apply (ae_mem_iff_measure_eq (hmeas hRneMeas).nullMeasurableSet).2
    rw [← Measure.map_apply (show Measurable (fun field => f field u) from hmeas) hRneMeas,
      hlaw, hRne]
    exact measure_univ.symm
  have hentry := entrance_count_le_at_firstSuccessfulCompletion_ae μ hnorm N R growth hR hgrowth
    lower upper duration hupper hbounded hcapacity M hcutoff r
  have hsub : {field | ¬ ∃ i ≤ T, (∃ e : Fin lower ↪ RootIndexed.TreeNode Root ℕ,
      ∀ j, e j ∈ Pop i field ∧
        RootIndexed.position (fun _ => 0) id (stage i field) (e j).1 (e j).2 ≤ c) ∧
        τ field = i} ≤ᵐ[P] Eᶜ ∪ f ⁻¹' large := by
    filter_upwards [hall, hentry] with field hmarks hentry₀ hbad
    by_cases hgood : field ∈ E
    · have htime : τ field ≤ (T : WithTop ℕ) := hgood.2
      have hfin : τ field ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top htime
      obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp hfin
      have hit : i ≤ T := WithTop.coe_le_coe.mp (hi.trans_le htime)
      have hτi : firstSuccessfulCompletion R growth hR lower upper duration r (left field) = i :=
        hi.symm
      obtain ⟨j, hj, hsplitj, hsucc, hbefore, hroot⟩ :=
        splitCycle_first_success_at_completion R growth hR lower upper duration r (left field)
          hmarks i hτi
      let k := splitCount R r j (left field)
      have hk : k < K := by
        have hidx : (τ field).untopD 0 - (duration + 1) = j := by
          rw [← hi, WithTop.untopD_coe]
          omega
        have hcount := hgood.1
        change splitCount R r ((τ field).untopD 0 - (duration + 1)) (left field) < K at hcount
        rwa [hidx] at hcount
      by_cases hpos : x + (K : ℝ) * M ≤
          Spine.pathPotential realPotential (f field) (trialGrowthRoot R k (f field))
      · exact Or.inr ⟨k, hk, hsucc, hbefore, Or.inr hpos⟩
      · exfalso
        apply hbad
        obtain ⟨j', hj', _, hcount⟩ := hentry₀ i hτi
        have heq : j' = j := by omega
        subst j'
        let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (j + 1) (left field)
        have hu : u.1 = r := growthTrialRootAt_root (lineages R hR) R r PUnit.unit (j + 1) (left field)
        have hbound : Spine.pathPotential realPotential (left field u.1) u.2 + M * duration ≤ c := by
          change trialGrowthRoot R k (f field) = u.2 at hroot
          rw [hu, ← hroot]
          exact (add_le_add_left (le_of_lt (lt_of_not_ge hpos)) _).trans hc
        obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
          (α := Fin lower) (by simpa using hcount)
        exact ⟨i, hit, ⟨e, fun j => by
          have hj := Finset.mem_filter.mp (he (Set.mem_range_self j))
          exact ⟨hj.1, hj.2.trans hbound⟩⟩, hi.symm⟩
    · exact Or.inl hgood
  exact (measure_mono_ae hsub).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hlarge))

/-- Up to the reset, the split leading to the growth trial and each of its
truncated edges cost at most the cutoff. The preceding spine edges are
bounded by the observed first-child positive displacements. -/
lemma growthTrial_position_le_cutoff_add_selectedMarkSum
    {Root : Type*}
    (B growth : Step.FiniteSelection ℕ ℝ) (hB : B.IsBoundedBy 2)
    (M : ℝ) (hM : 0 ≤ M)
    (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (r : Root) (k age upper : ℕ) (ω : RootIndexed.StepField Root ℕ ℝ)
    (hBmeas : Measurable B.select) :
    let R := firstOrBelowPotential B realPotential M
    let hR := firstOrBelowPotential_measurable B hBmeas realPotential M
    let mark j := ω r (selectedPath R r j ω)
    (∀ j ≤ k, (mark j).IsOrderedBy realPotential) →
    (∀ j < k, (B (mark j)).Nonempty) →
    splitEvent R r k ω →
    ∀ q ∈ capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit (k + 1) age ω,
      max 0 (Spine.pathPotential realPotential (ω q.1) q.2) ≤
        M * ((k + 1 + age : ℕ) : ℝ) +
          ∑ j ∈ Finset.range k, max 0 ((mark j).potentialValue' realPotential
            (firstSelectedSlot B (mark j))) := by
  intro R hR mark hordered hnonempty hsplit q hq
  let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) ω
  let S := ∑ j ∈ Finset.range k, max 0 ((mark j).potentialValue' realPotential
    (firstSelectedSlot B (mark j)))
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hsp := positivePart_le_cutoff_add_firstSelectedChildSum B hB realPotential M hM r k ω
    (fun j hj => hordered j hj.le) hnonempty
  have hgrow := rootedCapStoppedPopulation_pathPotential_le growth realPotential M hcutoff
    upper age ω u q hq
  have hroot := (GrowthTrial.root_at_split R hR r k ω hsplit).1
  have hsplitCard : 2 ≤ (R (mark k)).card := by
    simpa [splitEvent, splitBy, mark] using hsplit
  have hedge := (firstOrBelowPotential_edgePotentials_le_of_ordered B hB realPotential M
    (mark k) (hordered k le_rfl) hsplitCard).1
  have hbase : Spine.pathPotential realPotential (ω u.1) u.2 ≤ M * k + S + M := by
    change Spine.pathPotential realPotential (ω (growthTrialRootAt (lineages R hR) R r
      PUnit.unit (k + 1) ω).1) (growthTrialRootAt (lineages R hR) R r
        PUnit.unit (k + 1) ω).2 ≤ _
    rw [hroot, Spine.pathPotential_append, Spine.pathPotential_singleton]
    have hstep : (subtreeStepField (selectedPath R r k ω) (ω r) []).potentialValue'
        realPotential (firstSelectedSlot R (mark k)) ≤ M := by
      simpa [subtreeStepField, mark] using hedge
    exact add_le_add ((le_max_right 0 _).trans hsp) hstep
  change max 0 (Spine.pathPotential realPotential (ω q.1) q.2) ≤
    M * ((k + 1 + age : ℕ) : ℝ) + S
  apply max_le
  · exact add_nonneg (mul_nonneg hM (Nat.cast_nonneg _)) hS
  · calc
      _ ≤ Spine.pathPotential realPotential (ω u.1) u.2 + M * age := hgrow
      _ ≤ (M * k + S + M) + M * age := add_le_add hbase le_rfl
      _ = _ := by push_cast; ring

set_option maxHeartbeats 1000000 in
/-- At any age of the first successful trial, the corresponding descendants
can be compared to the actual selected population at that generation.
The parallel population supplies the pathwise comparison for these
particular descendants of the original trial. -/
lemma firstSuccessfulTrial_positionWitness_during_window_ae
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) :
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      ∀ k age : ℕ, age ≤ duration → τ field = ((k + 1 + duration : ℕ) : WithTop ℕ) →
        ∀ q ∈ capStoppedCandidate (lineages R hR) R growth upper r
            PUnit.unit (k + 1) age left,
          ∃ p ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
              (fun _ => 0) id trials.toFinset (k + 1 + age) field,
            RootIndexed.position (fun _ => 0) id
              (RootIndexed.restartedRealPositionNSelectedBRWField N {r}
                (fun _ => 0) id trials.toFinset (k + 1 + age) field) p.1 p.2 ≤
              RootIndexed.position (fun _ => 0) id left q.1 q.2 := by
  intro trials τ
  have hcomp (n : ℕ) := Coupling.positionWitness_ae μ hnorm N (fun _ => 0)
    R growth hR hgrowth upper duration hbounded hupper hcapacity r n
  filter_upwards [ae_all_iff.2 hcomp] with field hf
  intro left k age hage ht q hq
  let declarations : ℕ → Set (RootIndexed.StepField Root ℕ ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ successEvent R growth hR lower upper duration r k}
  have hfirst : firstDeclaredSuccess declarations left = ((k + 1 + duration : ℕ) : WithTop ℕ) := ht
  obtain ⟨j, hj, hs⟩ := ((firstDeclaredSuccess_eq_iff declarations left _).mp hfirst).1
  have hjk : j = k := by
    have h : j + 1 + duration = k + 1 + duration := WithTop.coe_injective hj
    omega
  subst j
  obtain ⟨halive, hsplit, _⟩ := hs
  exact hf (k + 1 + age) q (SelectedPath.Population.growthTrial_subset_during_window
    R growth hR upper duration r k age hage left halive hsplit hq)

/-- The pre-reset generation slice on the common pre-sampled tree. Once
the birth generation of the successful trial has been reached, its slice
is used through its completion generation. -/
noncomputable def trialRestartPopulationBeforeReset
    {Root : Type*} [DecidableEq (RootIndexed.TreeNode Root ℕ)]
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (lower upper duration : ℕ) (r : Root) (H : ℕ)
    (ω : RootIndexed.StepField Root ℕ ℝ) : Finset (RootIndexed.TreeNode Root ℕ) :=
  match firstSuccessfulCompletion R growth hR lower upper duration r ω with
  | ⊤ => {(r, selectedPath R r H ω)}
  | (n : ℕ) =>
    if H < n - duration then {(r, selectedPath R r H ω)}
    else if H ≤ n then capStoppedCandidate (lineages R hR) R growth upper r
      PUnit.unit (n - duration) (H - (n - duration)) ω
    else ∅

set_option maxHeartbeats 1000000 in
/-- Compare the pre-reset slice itself with the actual selected population.
The comparison is obtained by restricting the injection of the causal
population to the chosen slice. -/
lemma trialRestartPopulationBeforeReset_positionWitness_ae
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) :
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      ∀ H, isAlive R r H left →
        ∀ q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H left,
          ∃ p ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
              (fun _ => 0) id trials.toFinset H field,
            RootIndexed.position (fun _ => 0) id
              (RootIndexed.restartedRealPositionNSelectedBRWField N {r}
                (fun _ => 0) id trials.toFinset H field) p.1 p.2 ≤
              RootIndexed.position (fun _ => 0) id left q.1 q.2 := by
  intro trials
  have hcomp (H : ℕ) := Coupling.positionWitness_ae μ hnorm N (fun _ => 0)
    R growth hR hgrowth upper duration hbounded hupper hcapacity r H
  have hgrowthComp := firstSuccessfulTrial_positionWitness_during_window_ae
    μ hnorm N R growth hR hgrowth lower upper duration hupper hbounded hcapacity r
  filter_upwards [ae_all_iff.2 hcomp, hgrowthComp] with field hcompField hgrowthField
  intro left H hAlive q hq
  have hpath (hqpath : q = (r, selectedPath R r H left)) := by
    exact hcompField H q (hqpath ▸
      SelectedPath.Population.slice_contains_selectedPath R growth hR upper duration r H left hAlive)
  cases htime : firstSuccessfulCompletion R growth hR lower upper duration r left with
  | top =>
    apply hpath
    simpa only [trialRestartPopulationBeforeReset, htime, Finset.mem_singleton] using hq
  | coe n =>
    by_cases hbefore : H < n - duration
    · apply hpath
      simpa only [trialRestartPopulationBeforeReset, htime, ite_eq_left hbefore,
        Finset.mem_singleton] using hq
    by_cases hH : H ≤ n
    · let declarations : ℕ → Set (RootIndexed.StepField Root ℕ ℝ) := fun j =>
        {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = j ∧
          ω ∈ successEvent R growth hR lower upper duration r k}
      have ht : firstDeclaredSuccess declarations left = (n : WithTop ℕ) := htime
      obtain ⟨k, hk, _⟩ := ((firstDeclaredSuccess_eq_iff declarations left n).mp ht).1
      have hn : k + 1 + duration = n := WithTop.coe_injective hk
      have hborn : n - duration = k + 1 := by omega
      have hnotborn : ¬ H < k + 1 := by omega
      have hage : H - (k + 1) ≤ duration := by omega
      have hHage : k + 1 + (H - (k + 1)) = H := by omega
      have hmem : q ∈ capStoppedCandidate (lineages R hR) R growth upper r
          PUnit.unit (k + 1) (H - (k + 1)) left := by
        simpa only [trialRestartPopulationBeforeReset, htime, hborn, ite_eq_right hnotborn,
          ite_eq_left hH] using hq
      have h := hgrowthField k (H - (k + 1)) hage (htime.trans hk.symm) q hmem
      simpa only [hHage] using h
    · simp [trialRestartPopulationBeforeReset, htime, hbefore, hH] at hq

set_option maxHeartbeats 600000 in
/-- The same positive displacement envelope bounds the slice before the
reset and the maximum at which the original growth trial is reset. -/
lemma trialRestart_beforeReset_and_shift_le
    (B growth : Step.FiniteSelection ℕ ℝ) (hB : B.IsBoundedBy 2)
    (hBmeas : Measurable B.select) (M : ℝ) (hM : 0 ≤ M)
    (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (lower upper duration r H : ℕ) (ω : RootIndexed.StepField ℕ ℕ ℝ) :
    let R := firstOrBelowPotential B realPotential M
    let hR := firstOrBelowPotential_measurable B hBmeas realPotential M
    let τ := firstSuccessfulCompletion R growth hR lower upper duration r
    let mark j := ω r (selectedPath R r j ω)
    let envelope := M * H + ∑ j ∈ Finset.range H,
      firstSelectedSlotPositivePotential B realPotential (mark j)
    (∀ j, (mark j).IsOrderedBy realPotential) →
    (∀ j, (B (mark j)).Nonempty) →
    (∀ q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H ω,
      max 0 (RootIndexed.position (fun _ => 0) id ω q.1 q.2) ≤ envelope) ∧
    ∀ n ≤ H, τ ω = (n : WithTop ℕ) →
      max 0 (trialResetPositionAtGeneration R growth hR upper duration r n ω) ≤ envelope := by
  intro R hR τ mark envelope hordered hne
  have hnonneg (j : ℕ) : 0 ≤ firstSelectedSlotPositivePotential B realPotential (mark j) :=
    le_max_left _ _
  have hmono {n : ℕ} (hn : n ≤ H) : (∑ j ∈ Finset.range n,
      firstSelectedSlotPositivePotential B realPotential (mark j)) ≤
      ∑ j ∈ Finset.range H, firstSelectedSlotPositivePotential B realPotential (mark j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn) (fun j _ _ => hnonneg j)
  have hpos (q : RootIndexed.TreeNode ℕ ℕ) :
      RootIndexed.position (fun _ => 0) id ω q.1 q.2 =
        Spine.pathPotential realPotential (ω q.1) q.2 := by
    simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential, realPotential]
  have hpath : max 0 (RootIndexed.position (fun _ => 0) id ω r (selectedPath R r H ω)) ≤
      envelope := by
    rw [hpos (r, selectedPath R r H ω)]
    exact positivePart_le_cutoff_add_firstSelectedChildSum B hB realPotential M hM r H ω
      (fun j _ => hordered j) (fun j _ => hne j)
  let declared : ℕ → Set (RootIndexed.StepField ℕ ℕ ℝ) := fun n =>
    {field | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      field ∈ successEvent R growth hR lower upper duration r k}
  have hsplit {n : ℕ} (ht : τ ω = (n : WithTop ℕ)) :
      ∃ k, n = k + 1 + duration ∧ splitEvent R r k ω := by
    change firstDeclaredSuccess declared ω = (n : WithTop ℕ) at ht
    obtain ⟨k, hk, hs⟩ := ((firstDeclaredSuccess_eq_iff declared ω n).mp ht).1
    exact ⟨k, (WithTop.coe_injective hk).symm, hs.2.1⟩
  have hgrow (k age : ℕ) (hH : k + 1 + age ≤ H) (hs : splitEvent R r k ω)
      (q : RootIndexed.TreeNode ℕ ℕ)
      (hq : q ∈ capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit (k + 1) age ω) :
      max 0 (RootIndexed.position (fun _ => 0) id ω q.1 q.2) ≤ envelope := by
    rw [hpos]
    have hb := growthTrial_position_le_cutoff_add_selectedMarkSum B growth hB M hM
      hcutoff r k age upper ω hBmeas (fun j _ => hordered j) (fun j _ => hne j) hs q hq
    exact hb.trans (add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hH) hM)
      (hmono (show k ≤ H by omega)))
  constructor
  · intro q hq
    change q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H ω at hq
    cases ht : firstSuccessfulCompletion R growth hR lower upper duration r ω with
    | top =>
      have heq : q = (r, selectedPath R r H ω) := by
        simpa only [trialRestartPopulationBeforeReset, ht, Finset.mem_singleton] using hq
      simpa only [heq] using hpath
    | coe n =>
      by_cases hw : H < n - duration
      · have heq : q = (r, selectedPath R r H ω) := by
          simpa only [trialRestartPopulationBeforeReset, ht, ite_eq_left hw,
            Finset.mem_singleton] using hq
        simpa only [heq] using hpath
      by_cases hn : H ≤ n
      · obtain ⟨k, hk, hs⟩ := hsplit ht
        have hbirth : n - duration = k + 1 := by omega
        have hborn : ¬ H < k + 1 := by omega
        apply hgrow k (H - (k + 1)) (by omega) hs q
        simpa only [trialRestartPopulationBeforeReset, ht, hbirth, ite_eq_right hborn, ite_eq_left hn]
          using hq
      · simp [trialRestartPopulationBeforeReset, ht, hw, hn] at hq
  · intro n hn ht
    obtain ⟨k, rfl, hs⟩ := hsplit ht
    let s := capStoppedCandidate (lineages R hR) R growth upper r PUnit.unit (k + 1) duration ω
    unfold trialResetPositionAtGeneration
    simp only [Nat.add_sub_cancel]
    change max 0 (if h : s.Nonempty then s.sup' h _ else _) ≤ envelope
    by_cases hnonempty : s.Nonempty
    · rw [dite_eq_left hnonempty, max_le_iff, Finset.sup'_le_iff]
      refine ⟨(le_max_left _ _).trans hpath, fun q hq => ?_⟩
      have hdepth := rootedCapStoppedPopulation_node_depth growth upper ω
        (growthTrialRootAt (lineages R hR) R r PUnit.unit (k + 1) ω) q duration hq
      rw [growthTrialRootAt_depth] at hdepth
      rw [RootIndexed.positionAtGeneration, ite_eq_left hdepth]
      exact (le_max_right _ _).trans (hgrow k duration hn hs q hq)
    · rw [dite_eq_right hnonempty]
      exact max_le ((le_max_left _ _).trans hpath) ((le_max_left _ _).trans hpath)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Coupling.Population
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition

/-!
# Displacement within a bounded growth trial

## Internal proof declarations

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

This is the bounded-growth contribution to the entrance estimate in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open MeasureTheory
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

open Combinatorics.Branching.Step.FiniteSelection
open SelectedPath.GrowthTrial
open GrowthTrial.Population (capStoppedPopulation capStoppedPopulation_succ_parent
  rootedCapStoppedPopulation rootedCapStoppedPopulation_card_ge_of_growthTrialSuccess)


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
    have hpos := rootedCapStoppedPopulation_pathPotential_le growth realPotential
      M hcutoff upper duration left u q hq'
    have hs : RootIndexed.position (fun _ => 0) id left q.1 q.2 =
        Spine.pathPotential realPotential (left q.1) q.2 := by
      simp [RootIndexed.position, RootIndexed.displace, Spine.pathPotential, realPotential]
    change RootIndexed.position (fun _ => 0) id _ (dom q).1 (dom q).2 ≤
      RootIndexed.position (fun _ => 0) id left q.1 q.2 at hdom
    exact hdom.trans (hs.trans_le (hpos.trans (by gcongr)))
  · exact dom.injOn.mono fun _ hq => hmem hq

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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

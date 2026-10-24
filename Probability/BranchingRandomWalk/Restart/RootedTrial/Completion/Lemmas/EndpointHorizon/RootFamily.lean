/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.AtStoppingTime
import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Source-side endpoint roots: proof support

## Supporting declarations

* `selectedReserveSpineRestartSourceEndpointRankVector` ranks the causal source at the first
  successful completion time and provides a pointwise fallback when the target population is
  too small.
* `selectedReserveSpineRestartSourceEndpointRankVector_measurable` proves its stopped
  filtration measurability.
* `selectedReserveSpineRestartEndpointFreshRoots` uses target roots when present and source
  roots as a fallback, tagged in disjoint root summands.
* `selectedReserveSpineRestartEndpointFreshRoots_measurable` proves measurability of this
  finite random root family.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open Combinatorics.Branching.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

/-- Rank the causal source population itself at the first successful
completion time. This supplies a pointwise fallback for raw fields where the
rank-installed target happens to have too few particles; on every finite
successful completion the source has at least `lower` particles. -/
noncomputable def selectedReserveSpineRestartSourceEndpointRankVector
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) : Fin lower →
      RootIndexed.TreeNode Root α := by
  classical
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  exact particleRankVectorAtStoppingTime
    (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p)
    (fun n field => hsource.toFinset n field)
    lower (r, []) field

/-- The stopped source-rank vector is measurable in the first-success
completion filtration. -/
lemma selectedReserveSpineRestartSourceEndpointRankVector_measurable
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let value := fun n (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p
  let candidates := fun n field => hsource.toFinset n field
  have hτ : IsStoppingTime F τ := by
    simpa [τ, selectedReserveSpineRestartEndpointTime] using
      selectedReserveSpineRestartEndpointTime_isStoppingTime
        R growth hR hgrowth lower upper duration r
  have hdepth : ∀ n field p, p ∈ candidates n field → p.2.length = n := by
    intro n field p hp
    exact source.depth n field p ((hsource.mem_toFinset n field p).mp hp)
  have hfiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n] {field | candidates n field = s} := by
    exact hsource.measurable_toFinset n (measurableSet_singleton s)
  have hrange (n : ℕ) : (Set.range (candidates n)).Countable := Set.to_countable _
  have hkey (n : ℕ) (p q : RootIndexed.TreeNode Root α) : Measurable[F n]
      fun field => valueKey (value n field) q < valueKey (value n field) p := by
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F n
    exact Selection.NSelection.measurable_valueKey_lt
      (fun field z => value n field z)
      (fun z =>
        (RootIndexed.positionAtGeneration_measurable initialPosition id
          measurable_id n z.1 z.2).comp
          (RootIndexed.StepField.reindex_filtration_measurable Sum.inl n)) p q
  have hmeas := measurable_particleRankVectorAtStoppingTime F τ hτ value
    candidates hfiber hrange hkey lower (r, [])
  change Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
    (particleRankVectorAtStoppingTime τ value candidates lower (r, []))
  exact hmeas

/-- Endpoint roots for a fresh-field factorization. At a rank present in the
rank-installed target population, use the right-copy target particle. If a
raw exceptional field has too few target particles, use the matching rank
from the causal source on the left copy instead. The sum tag keeps the two
fallback populations disjoint. -/
noncomputable def selectedReserveSpineRestartEndpointFreshRoots
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
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) :
    Fin lower → (Root ⊕ Root) × Combinatorics.UlamHarris.TreeNode α :=
  fun i =>
    let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    if target = (r, []) then
      (Sum.inl r, (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).2)
    else
      (Sum.inr r, target.2)

/-- The mixed endpoint-root vector is measurable in the stopping-time
filtration. The branch test is measurable because the target rank vector is
measurable and its default node is a measurable singleton. -/
lemma selectedReserveSpineRestartEndpointFreshRoots_measurable
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (hnodePath : Measurable (fun p : RootIndexed.TreeNode Root α => p.2))
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root) :
    Measurable[(selectedReserveSpineRestartEndpointTime_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := (selectedReserveSpineRestartEndpointTime_isStoppingTime
    R growth hR hgrowth lower upper duration r).measurableSpace
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r
  let source := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r
  let roots := selectedReserveSpineRestartEndpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  have htarget : Measurable[F] target := by
    simpa [F, target] using
      selectedReserveSpineRestartEndpointRankVector_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hsource : Measurable[F] source := by
    simpa [F, source] using
      selectedReserveSpineRestartSourceEndpointRankVector_measurable initialPosition
        R growth hR hgrowth lower upper duration r
  have hcoord : ∀ i : Fin lower,
      Measurable[F] (fun field =>
        selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i) := by
    intro i
    change Measurable[F] (fun field => roots field i)
    let t := fun field => target field i
    let s := fun field => source field i
    have ht : Measurable[F] t := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ target)
      exact (measurable_pi_apply i).comp htarget
    have hs : Measurable[F] s := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ source)
      exact (measurable_pi_apply i).comp hsource
    have hdefault : MeasurableSet[F] {field | t field = (r, [])} :=
      ht (measurableSet_singleton (r, []))
    have htag : Measurable[F] (fun field =>
        if t field = (r, []) then (Sum.inl r : Root ⊕ Root) else Sum.inr r) :=
      Measurable.ite hdefault measurable_const measurable_const
    have hnode : Measurable[F] (fun field =>
        if t field = (r, []) then (s field).2 else (t field).2) :=
      Measurable.ite hdefault (hnodePath.comp hs) (hnodePath.comp ht)
    have hpair := htag.prodMk hnode
    have hrootEq : (fun field => roots field i) = fun field =>
        (if target field i = (r, []) then Sum.inl r else Sum.inr r,
          if target field i = (r, []) then (source field i).2 else (target field i).2) := by
      funext field
      by_cases h : target field i = (r, []) <;>
        simp [roots, selectedReserveSpineRestartEndpointFreshRoots, target, source, h]
    rw [hrootEq]
    exact hpair
  letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F
  exact measurable_pi_iff.mpr hcoord


end ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

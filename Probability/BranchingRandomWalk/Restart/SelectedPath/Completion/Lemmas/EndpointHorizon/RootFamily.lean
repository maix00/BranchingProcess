/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.Population
import Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Basic
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Causal
import Probability.Process.Stopping.Selection.Ranked
import MeasureTheory.Selection.NSelection.ByValue
import MeasureTheory.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Selected-path endpoint roots: proof support

## Internal proof declarations

* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank` ranks particles in the selected-path BRW population at the first
  successful completion time and provides a pointwise fallback when the first-`N` BRW population is
  too small.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank_measurable` proves its stopped
  filtration measurability.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots` uses first-`N` BRW roots when present and selected-path BRW roots
  as a fallback, tagged in disjoint root summands.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_measurable` proves measurability of this
  finite random root family.

For $i\in\mathrm{Fin}(\mathrm{lower})$, let $T_i$ be the first-`N` BRW rank node and
$S_i$ the selected-path BRW rank node. The mixed root $R_i$ uses the first-`N` rank unless
$T_i$ is the default node $(r,\varnothing)$, in which case it uses the selected-path BRW rank. The resulting vector is measurable with respect to the stopped domain
flow:
\[
 R_i=\begin{cases}
 (\operatorname{inl}(r),S_i.2),&T_i=(r,\varnothing),\\
 (\operatorname{inr}(r),T_i.2),&T_i\ne(r,\varnothing).
 \end{cases}
\]
Here $T_i$ and $S_i$ are the $i$th values of
`Restart.SelectedPath.Completion.endpointNodesByRank` and
`Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank`, respectively.
-/

section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open _root_.Combinatorics.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon

/-- Rank the causal selected-path BRW population itself at the first successful
completion time. This supplies a pointwise fallback for raw fields where the
rank-installed first-`N` BRW happens to have too few particles; on every finite
successful completion the selected-path BRW population has at least `lower` particles. -/
noncomputable def endpointNodesByRank
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
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  exact particleRankVectorAtStoppingTime
    (Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p)
    (fun n field => hselectedBRWPopulation.toFinset n field)
    lower (r, []) field

/-- The stopped selected-path BRW rank vector is measurable in the first-success
completion filtration. -/
lemma endpointNodesByRank_measurable
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
    Measurable[(Restart.SelectedPath.Completion.time_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)
  let τ := Restart.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  let selectedBRWEndpointRankVector := Restart.SelectedPath.Population.leftBRWFamily R growth hR hgrowth
    upper duration r
  let value := fun n (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.StepField.left field) p
  let candidates := fun n field => hselectedBRWPopulation.toFinset n field
  have hτ : IsStoppingTime F τ := by
    simpa [τ, Restart.SelectedPath.Completion.time] using
      Restart.SelectedPath.Completion.time_isStoppingTime
        R growth hR hgrowth lower upper duration r
  have hdepth : ∀ n field p, p ∈ candidates n field → p.2.length = n := by
    intro n field p hp
    exact selectedBRWEndpointRankVector.depth n field p ((hselectedBRWPopulation.mem_toFinset n field p).mp hp)
  have hfiber (n : ℕ) (s : Finset (RootIndexed.TreeNode Root α)) :
      MeasurableSet[F n] {field | candidates n field = s} := by
    exact hselectedBRWPopulation.measurable_toFinset n (measurableSet_singleton s)
  have hrange (n : ℕ) : (Set.range (candidates n)).Countable := Set.to_countable _
  have hkey (n : ℕ) (p q : RootIndexed.TreeNode Root α) : Measurable[F n]
      fun field => valueKey (value n field) q < valueKey (value n field) p := by
    let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F n
    exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
      (fun field z => value n field z)
      (fun z =>
        (RootIndexed.positionAtGeneration_measurable initialPosition id
          measurable_id n z.1 z.2).comp
          (RootIndexed.StepField.reindex_filtration_measurable Sum.inl n)) p q
  have hmeas := measurable_particleRankVectorAtStoppingTime F τ hτ value
    candidates hfiber hrange hkey lower (r, [])
  change Measurable[(Restart.SelectedPath.Completion.time_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
    (particleRankVectorAtStoppingTime τ value candidates lower (r, []))
  exact hmeas

/-- Endpoint roots for a fresh-field factorization. At a rank present in the
rank-installed first-`N` BRW population, use the right-copy first-`N` BRW particle. If a
raw exceptional field has too few first-`N` BRW particles, use the matching rank
from the causal selected-path BRW on the left copy instead. The sum tag keeps the two
fallback populations disjoint. -/
noncomputable def endpointFreshRoots
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
    let nSelectedBRWEndpointRankVector := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
      R growth hR hgrowth lower upper duration r field i
    if nSelectedBRWEndpointRankVector = (r, []) then
      (Sum.inl r, (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
        R growth hR hgrowth lower upper duration r field i).2)
    else
      (Sum.inr r, nSelectedBRWEndpointRankVector.2)

/-- The mixed endpoint-root vector is measurable in the stopping-time
filtration. The branch test is measurable because the first-`N` BRW rank vector is
measurable and its default node is a measurable singleton. -/
lemma endpointFreshRoots_measurable
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
    Measurable[(Restart.SelectedPath.Completion.time_isStoppingTime
      R growth hR hgrowth lower upper duration r).measurableSpace]
      (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r) := by
  classical
  let F := (Restart.SelectedPath.Completion.time_isStoppingTime
    R growth hR hgrowth lower upper duration r).measurableSpace
  let nSelectedBRWEndpointRankVector := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
    R growth hR hgrowth lower upper duration r
  let selectedBRWEndpointRankVector := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
    R growth hR hgrowth lower upper duration r
  let roots := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
    R growth hR hgrowth lower upper duration r
  have hnSelectedBRW : Measurable[F] nSelectedBRWEndpointRankVector := by
    simpa [F, nSelectedBRWEndpointRankVector] using
      Restart.SelectedPath.Completion.endpointNodesByRank_measurable N initialPosition
        R growth hR hgrowth lower upper duration r
  have hselectedBRWPopulation : Measurable[F] selectedBRWEndpointRankVector := by
    simpa [F, selectedBRWEndpointRankVector] using
      Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank_measurable initialPosition
        R growth hR hgrowth lower upper duration r
  have hcoord : ∀ i : Fin lower,
      Measurable[F] (fun field =>
        Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i) := by
    intro i
    change Measurable[F] (fun field => roots field i)
    let t := fun field => nSelectedBRWEndpointRankVector field i
    let s := fun field => selectedBRWEndpointRankVector field i
    have ht : Measurable[F] t := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ nSelectedBRWEndpointRankVector)
      exact (measurable_pi_apply i).comp hnSelectedBRW
    have hs : Measurable[F] s := by
      change Measurable[F] ((fun v : Fin lower → RootIndexed.TreeNode Root α => v i) ∘ selectedBRWEndpointRankVector)
      exact (measurable_pi_apply i).comp hselectedBRWPopulation
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
        (if nSelectedBRWEndpointRankVector field i = (r, []) then Sum.inl r else Sum.inr r,
          if nSelectedBRWEndpointRankVector field i = (r, []) then (selectedBRWEndpointRankVector field i).2 else (nSelectedBRWEndpointRankVector field i).2) := by
      funext field
      by_cases h : nSelectedBRWEndpointRankVector field i = (r, []) <;>
        simp [roots, Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots, nSelectedBRWEndpointRankVector, selectedBRWEndpointRankVector, h]
    rw [hrootEq]
    exact hpair
  letI : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α ℝ) := F
  exact measurable_pi_iff.mpr hcoord


end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon

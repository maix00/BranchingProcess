/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.RootFamily
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.Geometry
import all Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.FreshField
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.EndpointFreshField
import Combinatorics.UlamHarris.Relation
import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Fixed-horizon endpoint-law proof lemmas

The declarations in this module support the fixed-horizon population-law
result. They express the measurable pushforward, generation-wise population
measurability, and endpoint-specific law transfer needed by that result.
They are internal proof steps, not independent probability interfaces.

## Internal proof declarations

* `selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite`
  pushes the endpoint-position/fresh-field product law through a measurable
  fixed-horizon observable.
* `observedPosition_jointInitial_measurable`,
  `measurable_childrenAtGeneration_over_product`, and
  `selectedPopulationTotalized_jointInitial_measurable` establish the needed
  finite-horizon measurability.
* `selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite`
  specializes the pushforward identity to the selected population.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

/-- Any measurable fixed-horizon observable of the stopped endpoint positions
and their fresh descendants has the product-law distribution obtained by
starting from the actual endpoint positions. This is deliberately a fixed
horizon pushforward theorem; it does not identify the law at a random
remaining time. -/
lemma selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite
    {Root α Outcome : Type*} {lower : ℕ} [Countable α] [MeasurableSpace α]
    [MeasurableSpace Outcome]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (fresh : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField (Fin lower) α ℝ)
    (hpair : Measurable (fun field => (positions field, fresh field)))
    (future : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ → Outcome)
    (hfreshLaw : ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
      (fun field => (positions field, fresh field)) =
        (((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
          (RootIndexed.stepFieldLaw (Root := Fin lower) μ))
    (hfuture : Measurable future) :
    ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
        (fun field => future (positions field, fresh field)) =
      ((((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
        (RootIndexed.stepFieldLaw (Root := Fin lower) μ)).map future := by
  rw [show (fun field => future (positions field, fresh field)) =
      future ∘ (fun field => (positions field, fresh field)) by rfl,
    ← Measure.map_map hfuture hpair, hfreshLaw]

lemma observedPosition_jointInitial_measurable
    {lower : ℕ} {α : Type*} [MeasurableSpace α]
    (n : ℕ) (p : RootIndexed.TreeNode (Fin lower) α) :
    Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.observedPositionAtGeneration (fun i => z.1 i) id id n z.2 p) := by
  classical
  by_cases hp : p.2.length = n
  · have hinitial : Measurable (fun z : (Fin lower → ℝ) ×
        RootIndexed.StepField (Fin lower) α ℝ => z.1 p.1) :=
      (measurable_pi_apply p.1).comp measurable_fst
    have hdispField : Measurable[RootIndexed.stepFiltration
        (Root := Fin lower) (α := α) (X := ℝ) n]
        (fun field : RootIndexed.StepField (Fin lower) α ℝ =>
          Combinatorics.Branching.displaceWith id (field p.1) [] p.2) :=
      RootIndexed.displace_measurable id measurable_id p.1 [] p.2 n (by simp [hp])
    have hdisp : Measurable (fun z : (Fin lower → ℝ) ×
        RootIndexed.StepField (Fin lower) α ℝ =>
          Combinatorics.Branching.displaceWith id (z.2 p.1) [] p.2) := by
      have hle : RootIndexed.stepFiltration
          (Root := Fin lower) (α := α) (X := ℝ) n ≤
          (inferInstance : MeasurableSpace
            (RootIndexed.StepField (Fin lower) α ℝ)) :=
        (RootIndexed.stepFiltration (Root := Fin lower) (α := α) (X := ℝ)).le' n
      exact (hdispField.mono hle le_rfl).comp measurable_snd
    change Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        if p.2.length = n then
          z.1 p.1 + Combinatorics.Branching.displaceWith id
            (z.2 p.1) [] p.2 else 0)
    simp only [hp, ↓reduceIte]
    exact hinitial.add hdisp
  · change Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        if p.2.length = n then
          z.1 p.1 + Combinatorics.Branching.displaceWith id
            (z.2 p.1) [] p.2 else 0)
    simp [hp]

lemma measurable_childrenAtGeneration_over_product
    {Ω Root α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (n : ℕ)
    (parents : Ω → Finset (RootIndexed.TreeNode Root α))
    (hparents : Measurable parents)
    (field : Ω → RootIndexed.StepField Root α X) (hfield : Measurable field) :
    Measurable (fun ω => Combinatorics.Branching.Population.childrenAtGeneration n (parents ω) (field ω)) := by
  classical
  rw [measurable_set_iff]
  intro q
  by_cases hdepth : q.2.length = n + 1
  · have hnonempty : q.2 ≠ [] := by
      intro h
      simp [h] at hdepth
    let i := q.2.getLast hnonempty
    have hi : q.2.getLast? = some i :=
      List.getLast?_eq_some_getLast hnonempty
    have hparentDepth : (RootIndexed.parent q).2.length = n := by
      simp only [RootIndexed.parent]
      rw [List.length_dropLast, hdepth]
      omega
    have hparentMem : Measurable (fun ω => RootIndexed.parent q ∈ parents ω) :=
      (measurable_finset_mem (RootIndexed.parent q)).comp hparents
    have hsurviveField : MeasurableSet[
        RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) (n + 1)]
        {field : RootIndexed.StepField Root α X |
          Combinatorics.Branching.survive
            (field (RootIndexed.parent q).1 (RootIndexed.parent q).2) i} :=
      (RootIndexed.step_measurable (X := X) (RootIndexed.parent q).1
        (RootIndexed.parent q).2 (by omega))
        (Combinatorics.Branching.survive_measurableSet (X := X) i)
    have hsurviveFull : MeasurableSet
        {field : RootIndexed.StepField Root α X |
          Combinatorics.Branching.survive
            (field (RootIndexed.parent q).1 (RootIndexed.parent q).2) i} :=
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)).le'
        (n + 1) _ hsurviveField
    have hsurvive : Measurable (fun ω => Combinatorics.Branching.survive
        (field ω (RootIndexed.parent q).1 (RootIndexed.parent q).2) i) := by
      apply measurableSet_setOfPred.mp
      exact hsurviveFull.preimage hfield
    simpa [Combinatorics.Branching.Population.childrenAtGeneration, hdepth, hi] using hparentMem.and hsurvive
  · simp [Combinatorics.Branching.Population.childrenAtGeneration, hdepth]

lemma selectedPopulationTotalized_jointInitial_measurable
    {lower : ℕ} {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [OrderBot α]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeDecidableEq : DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [instFinTreeOrder : LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (N H : ℕ) :
    Measurable (fun z : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun i => z.1 i) id id H z.2) := by
  classical
  induction H with
  | zero => exact measurable_const
  | succ n ih =>
      let field : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ →
          RootIndexed.StepField (Fin lower) α ℝ := Prod.snd
      let parents := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun i => z.1 i) id id n z.2
      let value := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.observedPositionAtGeneration (fun i => z.1 i) id id (n + 1) z.2
      let candidates := fun z : (Fin lower → ℝ) ×
          RootIndexed.StepField (Fin lower) α ℝ =>
        Combinatorics.Branching.Population.childrenAtGeneration n (parents z) (field z)
      have hparents : Measurable parents := by
        simpa [parents] using ih
      have hfield : Measurable field := measurable_snd
      have hcandidates : Measurable candidates := by
        exact measurable_childrenAtGeneration_over_product n parents hparents
          field hfield
      -- `TreeNode` is a product type, so its generic product preorder can
      -- otherwise be chosen when elaborating the lexicographic value key.
      -- Use the explicit particle order required by first-`N` selection.
      letI : Preorder (RootIndexed.TreeNode (Fin lower) α) :=
        (inferInstance : LinearOrder (RootIndexed.TreeNode (Fin lower) α)).toPreorder
      have hkey : ∀ p q : RootIndexed.TreeNode (Fin lower) α,
          Measurable fun z =>
            Combinatorics.Selection.NSelection.valueKey
              (value z) q <
                Combinatorics.Selection.NSelection.valueKey
                  (value z) p := by
        intro p q
        exact Combinatorics.Selection.NSelection.measurable_valueKey_lt
          value (fun r => by
            simpa [value] using observedPosition_jointInitial_measurable (n + 1) r) p q
      change Measurable (fun z =>
        Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized
          N (value) candidates z)
      exact Combinatorics.Selection.NSelection.measurable_selectFirstNFromSetTotalized
        N value candidates hcandidates hkey

/-- Fixed-horizon first-`N` selection after a successful restart endpoint.
The selected population is a measurable function of the retained endpoint
positions and the fresh descendant field; the preceding joint-law theorem
therefore gives its distribution from those positions. The horizon `H` is a
fixed natural number, not the random time remaining in the original process. -/
lemma selectedReserveSpineRestartEndpointFixedHorizonPopulation_law_on_finite
    {Root α : Type*} {lower : ℕ} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace (RootIndexed.TreeNode (Fin lower) α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin lower) α)]
    [Countable (RootIndexed.TreeNode (Fin lower) α)]
    [DecidableEq (RootIndexed.TreeNode (Fin lower) α)]
    [LinearOrder (RootIndexed.TreeNode (Fin lower) α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (E : Set (RootIndexed.StepField (Root ⊕ Root) α ℝ))
    (positions : RootIndexed.StepField (Root ⊕ Root) α ℝ → Fin lower → ℝ)
    (fresh : RootIndexed.StepField (Root ⊕ Root) α ℝ →
      RootIndexed.StepField (Fin lower) α ℝ)
    (hpair : Measurable (fun field => (positions field, fresh field)))
    (hjoint : ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
      (fun field => (positions field, fresh field)) =
        (((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
          (RootIndexed.stepFieldLaw (Root := Fin lower) μ))
    (N H : ℕ) :
    ((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map
        (fun field => RootIndexed.selectedPopulationTotalized N Finset.univ
          (positions field) id id H (fresh field)) =
      ((((RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).restrict E).map positions).prod
        (RootIndexed.stepFieldLaw (Root := Fin lower) μ)).map
          (fun p => RootIndexed.selectedPopulationTotalized N Finset.univ
            p.1 id id H p.2) := by
  have hselected : Measurable (fun p : (Fin lower → ℝ) ×
      RootIndexed.StepField (Fin lower) α ℝ =>
        RootIndexed.selectedPopulationTotalized N Finset.univ p.1 id id H p.2) :=
    selectedPopulationTotalized_jointInitial_measurable N H
  have hpop := selectedReserveSpineRestartEndpointFixedHorizonObservable_law_on_finite
    μ E positions fresh
    hpair
    (fun p : (Fin lower → ℝ) × RootIndexed.StepField (Fin lower) α ℝ =>
      RootIndexed.selectedPopulationTotalized N Finset.univ p.1 id id H p.2)
    hjoint
    hselected
  simpa using hpop


end ProbabilityTheory.BranchingRandomWalk

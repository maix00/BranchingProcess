/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Restart.SelectedPath.Coupling.Population
import Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Basic
import all Probability.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.RootFamily
import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Causal
import Probability.Process.Stopping.Selection.Ranked
import MeasureTheory.Selection.NSelection.ByValue
import MeasureTheory.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

open ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Population

/-!
# Endpoint root properties: proof support

## Internal proof declarations

* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.success_of_finite` identifies every finite endpoint
  with a successful fixed-index candidate and its completion generation.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.card_ge_at_finite_endpoint` gives the selected-path BRW population's
  lower cardinality bound there, and `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.slice_root` identifies
  its root.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_depth` and
  `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_injective` give the depth and distinctness
  properties needed for a fresh descendant field.
* `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_eq_nSelectedBRW_of_card` identifies the fallback
  family with the nSelectedBRWEndpointRankVector when the first-`N` endpoint rank vector has at least `lower` particles;
  `Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_eq_nSelectedBRW_ae` gives that identity almost
  surely at a finite endpoint.

At a finite endpoint, the selected-path BRW population and fresh roots satisfy
\[
  |P_n^{\mathrm{selectedPath}}|\ge \mathrm{lower},\qquad
  \operatorname{depth}(r_i)=n,\qquad
  i\ne j\Longrightarrow r_i\ne r_j,
\]
and the fallback root family agrees with the first-`N` endpoint rank-vector roots almost
surely on that endpoint event.

-/

section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open _root_.Combinatorics.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon

/-- A finite endpoint time is exactly the end of one successful fixed-index
trial. -/
lemma success_of_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    ∃ k : ℕ, k + 1 + duration = n ∧
      RootIndexed.StepField.left field ∈
        Restart.SelectedPath.GrowthTrial.successEvent R growth hR
          lower upper duration r k := by
  let declarations : ℕ → Set (RootIndexed.StepField Root α ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ Restart.SelectedPath.GrowthTrial.successEvent R growth hR
        lower upper duration r k}
  have hfirst : firstDeclaredSuccess declarations (RootIndexed.StepField.left field) =
      (n : WithTop ℕ) := by
    simpa [Restart.SelectedPath.Completion.time,
      Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion, declarations] using htime
  have hdecl := (firstDeclaredSuccess_eq_iff declarations
    (RootIndexed.StepField.left field) n).mp hfirst
  obtain ⟨k, hkn, hsuccess⟩ := hdecl.1
  refine ⟨k, ?_, ?_⟩
  · exact WithTop.coe_injective hkn
  · simpa [declarations] using hsuccess

/-- At any finite first-success endpoint, the all-candidate causal selected-path BRW population
contains the requested number of particles, pathwise. -/
lemma card_ge_at_finite_endpoint
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    lower ≤ ((Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR
      hgrowth upper duration r).toFinset n field).card := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  obtain ⟨k, hkn, hsuccess⟩ := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.success_of_finite
    R growth hR hgrowth lower upper duration r field n htime
  have hsuccess' := hsuccess
  simp only [Restart.SelectedPath.GrowthTrial.successEvent, Set.mem_ofPred_eq] at hsuccess'
  rcases hsuccess' with ⟨halive, hsplit, hgrowthSuccess⟩
  have hcard := Restart.SelectedPath.Population.card_ge_of_success
    R growth hR lower upper duration r k (RootIndexed.StepField.left field)
    halive hsplit hupper (by simpa using hgrowthSuccess)
  have hselectedBRWPopulationEq : (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
      R growth hR hgrowth upper duration r).toFinset n field =
      Restart.SelectedPath.Population.slice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  rw [hselectedBRWPopulationEq]
  simpa [hkn] using hcard

/-- Every particle in the candidate-union selected-path BRW population belongs to the fixed initial
root `r`. This is useful when converting rooted particles to subtree
addresses for the stopped branching factorization theorem. -/
lemma slice_root
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (upper duration : ℕ) (r : Root) (n : ℕ)
    (field : RootIndexed.StepField Root α ℝ)
    (q : RootIndexed.TreeNode Root α)
    (hq : q ∈ Restart.SelectedPath.Population.slice R growth hR upper duration r n field) :
    q.1 = r := by
  classical
  have hcapRoot {root q : RootIndexed.TreeNode Root α} {age : ℕ}
      (hq : q ∈ rootedCapStoppedPopulation growth upper field root age) :
      q.1 = root.1 := by
    rw [rootedCapStoppedPopulation, Finset.mem_map] at hq
    obtain ⟨u, _, hqeq⟩ := hq
    exact (congrArg Prod.fst hqeq).symm
  rw [Restart.SelectedPath.Population.slice, Finset.mem_union] at hq
  rcases hq with hselectedPath | hcandidate
  · by_cases halive : Restart.SelectedPath.isAlive R r n field
    · have hnode : q = (r, Restart.selectedPath R r n field) := by
        simpa [halive] using hselectedPath
      simp [hnode]
    · simp [halive] at hselectedPath
  · obtain ⟨k, hk, hq⟩ :=
      (Restart.SelectedPath.GrowthTrial.mem_population_iff R growth hR upper duration r n field q).mp
        hcandidate
    let root := Restart.SelectedPath.GrowthTrial.growthTrialRootAt (Restart.SelectedPath.lineages R hR) R r
      PUnit.unit (k + 1) field
    have hroot : root.1 = r := by
      exact Restart.SelectedPath.GrowthTrial.growthTrialRootAt_root (Restart.SelectedPath.lineages R hR)
        R r PUnit.unit (k + 1) field
    exact (hcapRoot hq).trans hroot

/-- The mixed endpoint-root vector has the right absolute generation on every
finite successful path. Roots from the first-`N` BRW are used when available; roots from the selected-path BRW population
fill any missing first-`N` endpoint ranks on exceptional raw fields. -/
lemma endpointFreshRoots_depth
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) (i : Fin lower) :
    (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i).2.length = n := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := Restart.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  let Restart.SelectedPath.Population.family := Restart.SelectedPath.Population.leftBRWFamily R growth hR hgrowth
    upper duration r
  let selectedBRWOrderKey := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let selectedBRWPopulation := fun k field => hselectedBRWPopulation.toFinset k field
  have hselectedBRWPopulationCard := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hselectedBRWPopulationMem :
      Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
        R growth hR hgrowth lower upper duration r field i ∈ selectedBRWPopulation n field := by
    change particleRankVectorAtStoppingTime τ selectedBRWOrderKey selectedBRWPopulation lower (r, [])
      field i ∈ selectedBRWPopulation n field
    exact particleRankVectorAtStoppingTime_mem τ selectedBRWOrderKey selectedBRWPopulation lower (r, [])
      field n htime hselectedBRWPopulationCard i
  have hselectedBRWPopulationDepth :
      (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
        R growth hR hgrowth lower upper duration r field i).2.length = n := by
    exact Restart.SelectedPath.Population.family.depth n field _
      ((hselectedBRWPopulation.mem_toFinset n field _).mp (by simpa [selectedBRWPopulation] using hselectedBRWPopulationMem))
  let nSelectedBRWOrderKey := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        hselectedBRWPopulation.toFinset k field) p
  let nSelectedBRWPopulation := fun k field => RootIndexed.restartedRealPositionNSelectedBRWPopulation
    N {r} initialPosition id
    hselectedBRWPopulation.toFinset k field
  let nSelectedBRWEndpointRankVector := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
    R growth hR hgrowth lower upper duration r field i
  by_cases hdefault : nSelectedBRWEndpointRankVector = (r, [])
  · have hnode :
        (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 =
          (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
            R growth hR hgrowth lower upper duration r field i).2 := by
      simp [Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots, nSelectedBRWEndpointRankVector, hdefault]
    rw [hnode]
    exact hselectedBRWPopulationDepth
  · have hsome : particleAtRankByAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation i.1 field ≠ none := by
      intro hnone
      apply hdefault
      change (particleAtRankByAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation i.1 field).getD
          (r, []) = (r, [])
      simp [hnone]
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
    have hp' : particleAtRankBy (nSelectedBRWOrderKey n field) (nSelectedBRWPopulation n field) i.1 = some p := by
      have hstop : particleAtRankByAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation i.1 field = some p := hp.symm
      rw [particleAtRankByAtStoppingTime_eq_finite τ nSelectedBRWOrderKey nSelectedBRWPopulation i.1 field n
        (by simpa [τ] using htime)] at hstop
      exact hstop
    have hnSelectedBRWPopulationEq : nSelectedBRWEndpointRankVector = p := by
      change (particleAtRankByAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation i.1 field).getD
        (r, []) = p
      rw [hp.symm]
      rfl
    have hnSelectedBRWPopulationStage : particleAtRankBy (nSelectedBRWOrderKey n field)
        (nSelectedBRWPopulation n field) i.1 = some p := hp'
    have hmemNSelectedBRW : p ∈ nSelectedBRWPopulation n field :=
      (particleAtRankBy_eq_some_iff.mp hnSelectedBRWPopulationStage).1
    have hdepthNSelectedBRW := RootIndexed.selectedPopulationTotalized_depth
      N {r} initialPosition id id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p
      (by simpa [nSelectedBRWPopulation, RootIndexed.restartedRealPositionNSelectedBRWPopulation]
        using hmemNSelectedBRW)
    have hdepthNSelectedBRW' : p.2.length = n := hdepthNSelectedBRW
    have hnode :
        (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 = nSelectedBRWEndpointRankVector.2 := by
      simp [Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots, nSelectedBRWEndpointRankVector, hdefault]
    rw [hnode, hnSelectedBRWPopulationEq]
    exact hdepthNSelectedBRW'

/-- At a finite successful endpoint, the mixed root vector is injective.
Ranks on either side are distinct, and the left/right root tags separate the
fallback selected-path BRW particles from first-`N` endpoint-rank particles. -/
lemma endpointFreshRoots_injective
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    Function.Injective (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := Restart.SelectedPath.Completion.time R growth hR hgrowth
    lower upper duration r
  let hselectedBRWPopulation := Restart.SelectedPath.Population.leftBRWFamily_finiteSlices
    R growth hR hgrowth upper duration r
  let Restart.SelectedPath.Population.family := Restart.SelectedPath.Population.leftBRWFamily R growth hR hgrowth
    upper duration r
  let selectedBRWOrderKey := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let selectedBRWPopulation := fun k field => hselectedBRWPopulation.toFinset k field
  let nSelectedBRWOrderKey := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        hselectedBRWPopulation.toFinset k field) p
  let nSelectedBRWPopulation := fun k field => RootIndexed.restartedRealPositionNSelectedBRWPopulation
    N {r} initialPosition id
    hselectedBRWPopulation.toFinset k field
  have hselectedBRWPopulationCard := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hroot (i : Fin lower) :
      Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r field i =
        if Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
            R growth hR hgrowth lower upper duration r field i = (r, []) then
          (Sum.inl r, (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank
            initialPosition R growth hR hgrowth lower upper duration r field i).2)
        else (Sum.inr r, (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
          R growth hR hgrowth lower upper duration r field i).2) := by
    simp [Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots]
  have hselectedBRWPopulationSliceEq : selectedBRWPopulation n field =
      Restart.SelectedPath.Population.slice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hselectedBRWPopulationRoot (i : Fin lower) :
      (Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    apply Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.slice_root R growth hR upper duration r n
      (RootIndexed.StepField.left field)
    rw [← hselectedBRWPopulationSliceEq]
    change particleRankVectorAtStoppingTime τ selectedBRWOrderKey selectedBRWPopulation lower (r, [])
      field i ∈ selectedBRWPopulation n field
    exact particleRankVectorAtStoppingTime_mem τ selectedBRWOrderKey selectedBRWPopulation lower (r, [])
      field n htime hselectedBRWPopulationCard i
  have hnSelectedBRWPopulationRoot (i : Fin lower)
      (hne : Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
        R growth hR hgrowth lower upper duration r field i ≠ (r, [])) :
      (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    let t := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
      R growth hR hgrowth lower upper duration r field i
    have hmem : t ∈ nSelectedBRWPopulation n field := by
      change particleRankVectorAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation lower (r, [])
        field i ∈ nSelectedBRWPopulation n field
      have hne' := hne
      change particleRankVectorAtStoppingTime τ nSelectedBRWOrderKey nSelectedBRWPopulation lower
        (r, []) field i ≠ (r, []) at hne'
      exact particleRankVectorAtStoppingTime_mem_of_ne_default τ nSelectedBRWOrderKey nSelectedBRWPopulation
        lower (r, []) field n htime i hne'
    have hroot := RootIndexed.selectedPopulationTotalized_root_mem N {r}
      initialPosition id id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        hselectedBRWPopulation.toFinset n field) t
      (by simpa [nSelectedBRWPopulation, RootIndexed.restartedRealPositionNSelectedBRWPopulation] using hmem)
    simpa [t] using hroot
  intro i j hij
  let ti := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
    R growth hR hgrowth lower upper duration r field i
  let tj := Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
    R growth hR hgrowth lower upper duration r field j
  let si := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
    R growth hR hgrowth lower upper duration r field i
  let sj := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointNodesByRank initialPosition
    R growth hR hgrowth lower upper duration r field j
  have hi : ti = (r, []) ∨ ti ≠ (r, []) := eq_or_ne ti (r, [])
  have hj : tj = (r, []) ∨ tj ≠ (r, []) := eq_or_ne tj (r, [])
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hpath : si.2 = sj.2 := by
      have h := hij
      rw [hroot i, hroot j] at h
      simpa [ti, tj, si, sj, hi, hj] using congrArg Prod.snd h
    have hnodes : si = sj := Prod.ext (hselectedBRWPopulationRoot i |>.trans (hselectedBRWPopulationRoot j).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank τ selectedBRWOrderKey selectedBRWPopulation
      lower (r, []) field n htime hselectedBRWPopulationCard i
    have hrj := particleRankVectorAtStoppingTime_rank τ selectedBRWOrderKey selectedBRWPopulation
      lower (r, []) field n htime hselectedBRWPopulationCard j
    change rankBy (selectedBRWOrderKey n field) (selectedBRWPopulation n field) si = i.1 at hri
    change rankBy (selectedBRWOrderKey n field) (selectedBRWPopulation n field) sj = j.1 at hrj
    rw [hnodes] at hri
    apply Fin.ext
    omega
  · rw [hroot i, hroot j] at hij
    simp [ti, tj, si, sj, hi, hj] at hij
  ·
    rw [hroot i, hroot j] at hij
    simp [ti, tj, si, sj, hi, hj] at hij
  · have hnodes : ti = tj := by
      have h := hij
      rw [hroot i, hroot j] at h
      have hpath : ti.2 = tj.2 := by
        simpa [ti, tj, si, sj, hi, hj] using congrArg Prod.snd h
      exact Prod.ext (hnSelectedBRWPopulationRoot i hi |>.trans (hnSelectedBRWPopulationRoot j hj).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank_of_ne_default τ nSelectedBRWOrderKey
      nSelectedBRWPopulation lower (r, []) field n htime i hi
    have hrj := particleRankVectorAtStoppingTime_rank_of_ne_default τ nSelectedBRWOrderKey
      nSelectedBRWPopulation lower (r, []) field n htime j hj
    change rankBy (nSelectedBRWOrderKey n field) (nSelectedBRWPopulation n field) ti = i.1 at hri
    change rankBy (nSelectedBRWOrderKey n field) (nSelectedBRWPopulation n field) tj = j.1 at hrj
    rw [hnodes] at hri
    apply Fin.ext
    omega

/-- Whenever the rank-installed first-`N` endpoint rank vector has at least `lower` particles at the
finite endpoint, the mixed root vector is entirely on the first-`N` side.
The almost-sure coupling supplies this cardinality premise on first success. -/
lemma endpointFreshRoots_eq_nSelectedBRW_of_card
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ))
    (hcard : lower ≤ (RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
      initialPosition id
      (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field).card) (i : Fin lower) :
    Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i =
      (Sum.inr r, (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
        R growth hR hgrowth lower upper duration r field i).2) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  have hmem := particleRankVectorAtStoppingTime_mem
    (Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
        (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p)
    (fun n field => RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r}
      initialPosition id
      (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    lower (r, []) field n htime hcard i
  have hdepth := RootIndexed.selectedPopulationTotalized_depth N {r}
    initialPosition id id n
    (RootIndexed.restartedRealPositionNSelectedBRWField N {r} initialPosition id
      (Restart.SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
      R growth hR hgrowth lower upper duration r field i)
    (by simpa [RootIndexed.restartedRealPositionNSelectedBRWPopulation,
      Restart.SelectedPath.Completion.endpointNodesByRank,
      particleRankVectorAtStoppingTime] using hmem)
  have hne : Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
      R growth hR hgrowth lower upper duration r field i ≠ (r, []) := by
    intro hEq
    have hnpos : 0 < n := by
      obtain ⟨k, hkn, _⟩ := Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.success_of_finite
        R growth hR hgrowth lower upper duration r field n htime
      omega
    rw [hEq] at hdepth
    simp at hdepth
    omega
  simp [Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots, hne]

/-- Almost surely, on a finite first-success endpoint, the mixed root vector
used for fresh-field factorization is exactly the endpoint vector selected
from the rank-installed first-`N` BRW population. The selected-path branch only
totalizes exceptional raw fields where the first-`N` rank is absent. -/
lemma endpointFreshRoots_eq_nSelectedBRW_ae
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (initialPosition : Root → ℝ)
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ)
    (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      Restart.SelectedPath.Completion.time R growth hR hgrowth
        lower upper duration r field ≠ ⊤ →
      ∀ i : Fin lower,
        Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i =
        (Sum.inr r,
          (Restart.SelectedPath.Completion.endpointNodesByRank N initialPosition
            R growth hR hgrowth lower upper duration r field i).2) := by
  have hcomparison := Restart.SelectedPath.Coupling.firstSuccess_endpointComparison_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r
  filter_upwards [hcomparison] with field hfield
  intro hfinite i
  have hleft : Restart.SelectedPath.GrowthTrial.firstSuccessfulCompletion R growth hR
      lower upper duration r (RootIndexed.StepField.left field) ≠ ⊤ := by
    simpa [Restart.SelectedPath.Completion.time] using hfinite
  obtain ⟨_, n, htime, _, _, hcard, _⟩ := hfield hleft
  have htime' : Restart.SelectedPath.Completion.time R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ) := by
    simpa [Restart.SelectedPath.Completion.time] using htime
  exact Restart.SelectedPath.Completion.Lemmas.EndpointHorizon.endpointFreshRoots_eq_nSelectedBRW_of_card
    N initialPosition R growth hR hgrowth lower upper duration hupper r field n
    htime' hcard i


end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath.Completion.Lemmas.EndpointHorizon

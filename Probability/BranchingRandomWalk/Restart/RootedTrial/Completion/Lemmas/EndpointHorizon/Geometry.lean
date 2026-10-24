/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Coupling.ReserveSpine
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Endpoint
import Probability.BranchingRandomWalk.Restart.RootedTrial.Completion.Lemmas.EndpointHorizon.RootFamily
import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.AtStoppingTime
import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization

/-!
# Endpoint root properties: proof support

## Supporting declarations

* `selectedReserveSpineRestartEndpoint_success_of_finite` identifies every finite endpoint
  with a successful fixed-index candidate and its completion generation.
* `selectedReserveSpineRestartSource_card_ge_at_finite_endpoint` gives the source population's
  lower cardinality bound there, and `selectedReserveSpineRestartSourceSlice_root` identifies
  its root.
* `selectedReserveSpineRestartEndpointFreshRoots_depth` and
  `selectedReserveSpineRestartEndpointFreshRoots_injective` give the depth and distinctness
  properties needed for a fresh descendant field.
* `selectedReserveSpineRestartEndpointFreshRoots_eq_target_of_card` identifies the fallback
  family with the target when the target has at least `lower` particles;
  `selectedReserveSpineRestartEndpointFreshRoots_eq_target_ae` gives that identity almost
  surely at a finite endpoint.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open Combinatorics.Branching.Selection.NSelection

namespace ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

/-- A finite endpoint time is exactly the end of one successful fixed-index
trial. -/
lemma selectedReserveSpineRestartEndpoint_success_of_finite
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select) (lower upper duration : ℕ) (r : Root)
    (field : RootIndexed.StepField (Root ⊕ Root) α ℝ) (n : ℕ)
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    ∃ k : ℕ, k + 1 + duration = n ∧
      RootIndexed.StepField.left field ∈
        selectedReserveSpineCandidateSuccessEvent R growth hR
          lower upper duration r k := by
  let declarations : ℕ → Set (RootIndexed.StepField Root α ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
        lower upper duration r k}
  have hfirst : firstDeclaredSuccess declarations (RootIndexed.StepField.left field) =
      (n : WithTop ℕ) := by
    simpa [selectedReserveSpineRestartEndpointTime,
      selectedReserveSpineFirstSuccessfulCandidateCompletion, declarations] using htime
  have hdecl := (firstDeclaredSuccess_eq_iff declarations
    (RootIndexed.StepField.left field) n).mp hfirst
  obtain ⟨k, hkn, hsuccess⟩ := hdecl.1
  refine ⟨k, ?_, ?_⟩
  · exact WithTop.coe_injective hkn
  · simpa [declarations] using hsuccess

/-- At any finite first-success endpoint, the all-candidate causal source
contains the requested number of particles, pathwise. -/
lemma selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
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
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    lower ≤ ((selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR
      hgrowth upper duration r).toFinset n field).card := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  obtain ⟨k, hkn, hsuccess⟩ := selectedReserveSpineRestartEndpoint_success_of_finite
    R growth hR hgrowth lower upper duration r field n htime
  have hsuccess' := hsuccess
  simp only [selectedReserveSpineCandidateSuccessEvent, Set.mem_ofPred_eq] at hsuccess'
  rcases hsuccess' with ⟨halive, hsplit, hgrowthSuccess⟩
  have hcard := selectedReserveSpineRestartSource_card_ge_of_candidate_success
    R growth hR lower upper duration r k (RootIndexed.StepField.left field)
    halive hsplit hupper (by simpa using hgrowthSuccess)
  have hsourceEq : (selectedReserveSpineRestartSourceOnLeft_finiteSlices
      R growth hR hgrowth upper duration r).toFinset n field =
      selectedReserveSpineRestartSourceSlice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  rw [hsourceEq]
  simpa [hkn] using hcard

/-- Every particle in the candidate-union source belongs to the fixed initial
root `r`. This is useful when converting rooted particles to subtree
addresses for the stopped branching factorization theorem. -/
lemma selectedReserveSpineRestartSourceSlice_root
    {Root α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α ℝ) (hR : Measurable R.select)
    (upper duration : ℕ) (r : Root) (n : ℕ)
    (field : RootIndexed.StepField Root α ℝ)
    (q : RootIndexed.TreeNode Root α)
    (hq : q ∈ selectedReserveSpineRestartSourceSlice R growth hR upper duration r n field) :
    q.1 = r := by
  classical
  have hcapRoot {root q : RootIndexed.TreeNode Root α} {age : ℕ}
      (hq : q ∈ rootedCapStoppedPopulation growth upper field root age) :
      q.1 = root.1 := by
    rw [rootedCapStoppedPopulation, Finset.mem_map] at hq
    obtain ⟨u, _, hqeq⟩ := hq
    exact (congrArg Prod.fst hqeq).symm
  rw [selectedReserveSpineRestartSourceSlice, Finset.mem_union] at hq
  rcases hq with hspine | hcandidate
  · by_cases halive : selectedReserveSpineAlive R r n field
    · have hnode : q = (r, selectedReserveSpinePath R r n field) := by
        simpa [halive] using hspine
      simp [hnode]
    · simp [halive] at hspine
  · obtain ⟨k, hk, hq⟩ :=
      (mem_selectedReserveSpineCandidatePopulation_iff R growth hR upper duration r n field q).mp
        hcandidate
    let root := (selectedReserveSpineLineages R hR).firstChildRootAt R r
      PUnit.unit (k + 1) field
    have hroot : root.1 = r := by
      exact (selectedReserveSpineLineages R hR).firstChildRootAt_root
        R r PUnit.unit (k + 1) field
    exact (hcapRoot hq).trans hroot

/-- The mixed endpoint-root vector has the right absolute generation on every
finite successful path. Target roots are used when available; source roots
fill any missing target ranks on exceptional raw fields. -/
lemma selectedReserveSpineRestartEndpointFreshRoots_depth
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
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) (i : Fin lower) :
    (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i).2.length = n := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let sourceValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let sourceSet := fun k field => hsource.toFinset k field
  have hsourceCard := selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hsourceMem :
      selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i ∈ sourceSet n field := by
    change particleRankVectorAtStoppingTime τ sourceValue sourceSet lower (r, [])
      field i ∈ sourceSet n field
    exact particleRankVectorAtStoppingTime_mem τ sourceValue sourceSet lower (r, [])
      field n htime hsourceCard i
  have hsourceDepth :
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).2.length = n := by
    exact source.depth n field _
      ((hsource.mem_toFinset n field _).mp (by simpa [sourceSet] using hsourceMem))
  let targetValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset k field) p
  let targetSet := fun k field => RootIndexed.restartedRealPositionMatchedPopulation
    N {r} initialPosition id
    hsource.toFinset k field
  let target := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field i
  by_cases hdefault : target = (r, [])
  · have hnode :
        (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 =
          (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
            R growth hR hgrowth lower upper duration r field i).2 := by
      simp [selectedReserveSpineRestartEndpointFreshRoots, target, hdefault]
    rw [hnode]
    exact hsourceDepth
  · have hsome : particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field ≠ none := by
      intro hnone
      apply hdefault
      change (particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field).getD
          (r, []) = (r, [])
      simp [hnone]
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hsome
    have hp' : particleAtRankBy (targetValue n field) (targetSet n field) i.1 = some p := by
      have hstop : particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field = some p := hp.symm
      rw [particleAtRankByAtStoppingTime_eq_finite τ targetValue targetSet i.1 field n
        (by simpa [τ] using htime)] at hstop
      exact hstop
    have htargetEq : target = p := by
      change (particleAtRankByAtStoppingTime τ targetValue targetSet i.1 field).getD
        (r, []) = p
      rw [hp.symm]
      rfl
    have htargetStage : particleAtRankBy (targetValue n field)
        (targetSet n field) i.1 = some p := hp'
    have hmemTarget : p ∈ targetSet n field :=
      (particleAtRankBy_eq_some_iff.mp htargetStage).1
    have hdepthTarget := RootIndexed.selectedPopulationTotalized_depth
      N {r} initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p
      (by simpa [targetSet, RootIndexed.restartedRealPositionMatchedPopulation]
        using hmemTarget)
    have hdepthTarget' : p.2.length = n := hdepthTarget
    have hnode :
        (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i).2 = target.2 := by
      simp [selectedReserveSpineRestartEndpointFreshRoots, target, hdefault]
    rw [hnode, htargetEq]
    exact hdepthTarget'

/-- At a finite successful endpoint, the mixed root vector is injective.
Ranks on either side are distinct, and the left/right root tags separate the
fallback source particles from target particles. -/
lemma selectedReserveSpineRestartEndpointFreshRoots_injective
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
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ)) :
    Function.Injective (selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  let τ := selectedReserveSpineRestartEndpointTime R growth hR hgrowth
    lower upper duration r
  let hsource := selectedReserveSpineRestartSourceOnLeft_finiteSlices
    R growth hR hgrowth upper duration r
  let source := selectedReserveSpineRestartSourceOnLeft R growth hR hgrowth
    upper duration r
  let sourceValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p
  let sourceSet := fun k field => hsource.toFinset k field
  let targetValue := fun k (field : RootIndexed.StepField (Root ⊕ Root) α ℝ)
      (p : RootIndexed.TreeNode Root α) =>
    RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset k field) p
  let targetSet := fun k field => RootIndexed.restartedRealPositionMatchedPopulation
    N {r} initialPosition id
    hsource.toFinset k field
  have hsourceCard := selectedReserveSpineRestartSource_card_ge_at_finite_endpoint
    R growth hR hgrowth lower upper duration hupper r field n htime
  have hroot (i : Fin lower) :
      selectedReserveSpineRestartEndpointFreshRoots N initialPosition
        R growth hR hgrowth lower upper duration r field i =
        if selectedReserveSpineRestartEndpointRankVector N initialPosition
            R growth hR hgrowth lower upper duration r field i = (r, []) then
          (Sum.inl r, (selectedReserveSpineRestartSourceEndpointRankVector
            initialPosition R growth hR hgrowth lower upper duration r field i).2)
        else (Sum.inr r, (selectedReserveSpineRestartEndpointRankVector N initialPosition
          R growth hR hgrowth lower upper duration r field i).2) := by
    simp [selectedReserveSpineRestartEndpointFreshRoots]
  have hsourceSliceEq : sourceSet n field =
      selectedReserveSpineRestartSourceSlice R growth hR upper duration r n
        (RootIndexed.StepField.left field) := by
    apply Finset.coe_injective
    rw [RootIndexed.CausalPopulation.FiniteSlices.coe_toFinset]
    rfl
  have hsourceRoot (i : Fin lower) :
      (selectedReserveSpineRestartSourceEndpointRankVector initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    apply selectedReserveSpineRestartSourceSlice_root R growth hR upper duration r n
      (RootIndexed.StepField.left field)
    rw [← hsourceSliceEq]
    change particleRankVectorAtStoppingTime τ sourceValue sourceSet lower (r, [])
      field i ∈ sourceSet n field
    exact particleRankVectorAtStoppingTime_mem τ sourceValue sourceSet lower (r, [])
      field n htime hsourceCard i
  have htargetRoot (i : Fin lower)
      (hne : selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i ≠ (r, [])) :
      (selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).1 = r := by
    let t := selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i
    have hmem : t ∈ targetSet n field := by
      change particleRankVectorAtStoppingTime τ targetValue targetSet lower (r, [])
        field i ∈ targetSet n field
      have hne' := hne
      change particleRankVectorAtStoppingTime τ targetValue targetSet lower
        (r, []) field i ≠ (r, []) at hne'
      exact particleRankVectorAtStoppingTime_mem_of_ne_default τ targetValue targetSet
        lower (r, []) field n htime i hne'
    have hroot := RootIndexed.selectedPopulationTotalized_root_mem N {r}
      initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        hsource.toFinset n field) t
      (by simpa [targetSet, RootIndexed.restartedRealPositionMatchedPopulation] using hmem)
    simpa [t] using hroot
  intro i j hij
  let ti := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field i
  let tj := selectedReserveSpineRestartEndpointRankVector N initialPosition
    R growth hR hgrowth lower upper duration r field j
  let si := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r field i
  let sj := selectedReserveSpineRestartSourceEndpointRankVector initialPosition
    R growth hR hgrowth lower upper duration r field j
  have hi : ti = (r, []) ∨ ti ≠ (r, []) := eq_or_ne ti (r, [])
  have hj : tj = (r, []) ∨ tj ≠ (r, []) := eq_or_ne tj (r, [])
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hpath : si.2 = sj.2 := by
      have h := hij
      rw [hroot i, hroot j] at h
      simpa [ti, tj, si, sj, hi, hj] using congrArg Prod.snd h
    have hnodes : si = sj := Prod.ext (hsourceRoot i |>.trans (hsourceRoot j).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank τ sourceValue sourceSet
      lower (r, []) field n htime hsourceCard i
    have hrj := particleRankVectorAtStoppingTime_rank τ sourceValue sourceSet
      lower (r, []) field n htime hsourceCard j
    change rankBy (sourceValue n field) (sourceSet n field) si = i.1 at hri
    change rankBy (sourceValue n field) (sourceSet n field) sj = j.1 at hrj
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
      exact Prod.ext (htargetRoot i hi |>.trans (htargetRoot j hj).symm) hpath
    have hri := particleRankVectorAtStoppingTime_rank_of_ne_default τ targetValue
      targetSet lower (r, []) field n htime i hi
    have hrj := particleRankVectorAtStoppingTime_rank_of_ne_default τ targetValue
      targetSet lower (r, []) field n htime j hj
    change rankBy (targetValue n field) (targetSet n field) ti = i.1 at hri
    change rankBy (targetValue n field) (targetSet n field) tj = j.1 at hrj
    rw [hnodes] at hri
    apply Fin.ext
    omega

/-- Whenever the rank-installed target has at least `lower` particles at the
finite endpoint, the mixed root vector is entirely on the target/right side.
The almost-sure coupling supplies this cardinality premise on first success. -/
lemma selectedReserveSpineRestartEndpointFreshRoots_eq_target_of_card
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
    (htime : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ))
    (hcard : lower ≤ (RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field).card) (i : Fin lower) :
    selectedReserveSpineRestartEndpointFreshRoots N initialPosition
      R growth hR hgrowth lower upper duration r field i =
      (Sum.inr r, (selectedReserveSpineRestartEndpointRankVector N initialPosition
        R growth hR hgrowth lower upper duration r field i).2) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode Root α) := LinearOrder.toDecidableEq
  have hmem := particleRankVectorAtStoppingTime_mem
    (selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r)
    (fun n field p => RootIndexed.observedPositionAtGeneration initialPosition id id n
      (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
        (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
          upper duration r).toFinset n field) p)
    (fun n field => RootIndexed.restartedRealPositionMatchedPopulation N {r}
      initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    lower (r, []) field n htime hcard i
  have hdepth := RootIndexed.selectedPopulationTotalized_depth N {r}
    initialPosition id id n
    (RootIndexed.restartedRealPositionMatchedField N {r} initialPosition id
      (selectedReserveSpineRestartSourceOnLeft_finiteSlices R growth hR hgrowth
        upper duration r).toFinset n field)
    (selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i)
    (by simpa [RootIndexed.restartedRealPositionMatchedPopulation,
      selectedReserveSpineRestartEndpointRankVector,
      particleRankVectorAtStoppingTime] using hmem)
  have hne : selectedReserveSpineRestartEndpointRankVector N initialPosition
      R growth hR hgrowth lower upper duration r field i ≠ (r, []) := by
    intro hEq
    have hnpos : 0 < n := by
      obtain ⟨k, hkn, _⟩ := selectedReserveSpineRestartEndpoint_success_of_finite
        R growth hR hgrowth lower upper duration r field n htime
      omega
    rw [hEq] at hdepth
    simp at hdepth
    omega
  simp [selectedReserveSpineRestartEndpointFreshRoots, hne]

/-- Almost surely, on a finite first-success endpoint, the mixed root vector
used for fresh-field factorization is exactly the endpoint vector selected
from the rank-installed target population. The source-tagged branch only
totalizes exceptional raw fields where the target rank is absent. -/
lemma selectedReserveSpineRestartEndpointFreshRoots_eq_target_ae
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
      selectedReserveSpineRestartEndpointTime R growth hR hgrowth
        lower upper duration r field ≠ ⊤ →
      ∀ i : Fin lower,
        selectedReserveSpineRestartEndpointFreshRoots N initialPosition
          R growth hR hgrowth lower upper duration r field i =
        (Sum.inr r,
          (selectedReserveSpineRestartEndpointRankVector N initialPosition
            R growth hR hgrowth lower upper duration r field i).2) := by
  have hcomparison := selectedReserveSpineFirstSuccess_endpointComparison_ae
    μ hnorm N initialPosition R growth hR hgrowth lower upper duration hupper
    hbounded hcapacity r
  filter_upwards [hcomparison] with field hfield
  intro hfinite i
  have hleft : selectedReserveSpineFirstSuccessfulCandidateCompletion R growth hR
      lower upper duration r (RootIndexed.StepField.left field) ≠ ⊤ := by
    simpa [selectedReserveSpineRestartEndpointTime] using hfinite
  obtain ⟨_, n, htime, _, _, hcard, _⟩ := hfield hleft
  have htime' : selectedReserveSpineRestartEndpointTime R growth hR hgrowth
      lower upper duration r field = (n : WithTop ℕ) := by
    simpa [selectedReserveSpineRestartEndpointTime] using htime
  exact selectedReserveSpineRestartEndpointFreshRoots_eq_target_of_card
    N initialPosition R growth hR hgrowth lower upper duration hupper r field n
    htime' hcard i


end ProbabilityTheory.BranchingRandomWalk.Completion.Lemmas.EndpointHorizon

/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Combinatorics.UlamHarris.Relation

import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Window
import Probability.Process.Path.Restart.Basic

/-!
# Embedding first-stage corridor successes into the killed population

This module provides the pathwise population embedding used in Chapter 3,
Lemma 3.5 of WANG Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring*.

## Internal proof declarations

Let `F` be a root-indexed step field, and put
\[
  C_{\ell}=\operatorname{affineCorridorThrough}
    (\ell,-bL,0,bL,(-b+v)L),\qquad L=\log N.
\]
For a positive-a corridor path, write `X_k` for its root-relative position at
generation `k` under the restart anchor and `W_k` for the restarted window.
For the positive-a statements, `K_n(F)` denotes the generation-`n` slice of
the restarted population.
Explicitly,
\[
  X_k(r,u,F)=\operatorname{relativePositionAtGeneration}
    (0,\mathrm{id},\operatorname{restartAnchor}(\ell,k),k,(r,u.take(k)),F),
  \qquad
  W_k=\operatorname{positiveARestartedWindow}
    (\ell,\ell_N,L,b,v,c,\kappa,k).
\]

* `positiveA_corridorPath_mem_restartedWindow`:
  \[
    \operatorname{Spine.pathHistory}(\mathrm{realPotential},\ell,0,F(r),u)
      \in C_{\ell}
      \Longrightarrow
      \forall k\le\ell,\quad
      \operatorname{relativePositionAtGeneration}
        (0,\mathrm{id},\operatorname{restartAnchor}(\ell,k),k,
          (r,u.take(k)),F)
      \in \operatorname{positiveARestartedWindow}
        (\ell,\ell_N,L,b,v,c,\kappa,k).
  \]
* `positiveASuccessfulRoots` defines
  \[
    R_{m,\ell}(F)=\{r\in\operatorname{Fin}(m):
      F(r)\in\operatorname{hasPathHistoryIn}_{\mathbb N}
        (\mathrm{realPotential},\ell,0,C_{\ell})\}.
  \]
* `positiveA_successfulRoots_card_le_killedPopulation` and
  `ae_positiveA_successfulRoots_card_le_killedPopulation` give,
  respectively, the pathwise and almost-sure inequalities
  \[
    \#R_{m,\ell}(F)\le\#K_{\ell}(F).
  \]
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path

/-- The first-stage affine corridor is exactly the root-relative part of the
restarted schedule through the cutoff. -/
lemma positiveA_corridorPath_mem_restartedWindow
    {Root : Type*} (ell ellN : ℕ) (logN b v c κ : ℝ)
    (field : RootIndexed.StepField Root ℕ ℝ) (r : Root)
    (u : List ℕ) (hu : u.length = ell)
    (hcorridor : Spine.pathHistory realPotential ell 0 (field r) u ∈
      affineCorridorThrough ell (-b * logN) 0 (b * logN)
        ((-b + v) * logN)) :
    ∀ k ≤ ell,
      RootIndexed.relativePositionAtGeneration (fun _ : Root => 0) id
        (restartAnchor ell k) k (r, u.take k) field ∈
          positiveARestartedWindow ell ellN logN b v c κ k := by
  intro k hk
  let j : Fin (ell + 1) := ⟨k, by omega⟩
  have hcoord := hcorridor.1 j
  have hhistory :
      RootIndexed.relativePositionAtGeneration (fun _ : Root => 0) id
          (restartAnchor ell k) k (r, u.take k) field =
        Spine.pathHistory realPotential ell 0 (field r) u j := by
    rw [restartAnchor_eq_zero hk]
    simp [j, RootIndexed.relativePositionAtGeneration,
      RootIndexed.positionAtGeneration, RootIndexed.position,
      RootIndexed.displace, Spine.pathHistory, Spine.pathPotential,
      List.length_take, hu, Nat.min_eq_left hk, realPotential]
  rw [hhistory]
  by_cases hkle : k < ell
  · have hbounds :
        -b * logN ≤ Spine.pathHistory realPotential ell 0 (field r) u j ∧
          Spine.pathHistory realPotential ell 0 (field r) u j ≤ 0 := by
      constructor
      · simpa [j, mul_zero, mul_comm] using hcoord.1
      · have := hcoord.2
        have harith : -b * logN + b * logN = 0 := by ring
        simpa [j, mul_zero, harith, add_comm] using this
    simpa [positiveARestartedWindow, hkle] using hbounds
  · have hkeq : k = ell := by omega
    subst k
    have hbounds :
        -b * logN ≤ Spine.pathHistory realPotential ell 0 (field r) u j ∧
          Spine.pathHistory realPotential ell 0 (field r) u j ≤
            (-b + v) * logN := by
      constructor
      · simpa [j, mul_zero, mul_comm] using hcoord.1
      · simpa [j, mul_zero, mul_comm] using hcorridor.2
    simpa [positiveARestartedWindow] using hbounds

/-- Distinct successful initial root labels produce distinct particles in the
actual generation-`ell` restarted killed population. -/
noncomputable def positiveASuccessfulRoots
    (m ell : ℕ) (logN b v : ℝ)
    (field : RootIndexed.StepField (Fin m) ℕ ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun r =>
    field r ∈ hasPathHistoryIn (ι := ℕ) realPotential ell 0
      (affineCorridorThrough ell (-b * logN) 0 (b * logN)
        ((-b + v) * logN))

lemma positiveA_successfulRoots_card_le_killedPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RootIndexed.StepField (Fin m) ℕ ℝ)
    (hweight : ∀ r u,
      totalPotentialWeight realPotential (-1) (field r u) ≠ ∞) :
    let successfulRoots := positiveASuccessfulRoots
      m ell logN b v field
    let initial := RootIndexed.initialPopulation (α := ℕ)
      (Finset.univ : Finset (Fin m))
    let window := positiveARestartedWindow ell ellN logN b v c κ
    let upper := positiveAWindowUpper ell ellN logN b v c κ
    let populationFinite :=
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
        (fun _ : Fin m => 0) id measurable_id initial
        (by simp [initial, RootIndexed.mem_initialPopulation_iff])
        ell window (measurableSet_positiveARestartedWindow
          ell ellN logN b v c κ)
        upper (positiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
    successfulRoots.card ≤ (populationFinite.toFinset ell field).card := by
  classical
  let corridor := affineCorridorThrough ell (-b * logN) 0
    (b * logN) ((-b + v) * logN)
  let successfulRoots : Finset (Fin m) :=
    positiveASuccessfulRoots m ell logN b v field
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  let window := positiveARestartedWindow ell ellN logN b v c κ
  let upper := positiveAWindowUpper ell ellN logN b v c κ
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  let population := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell window
    (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  have populationFinite : population.FiniteSlices := by
    dsimp [population]
    exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
      (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell window
      (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
      upper (positiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
  let actual := populationFinite.toFinset ell field
  have hsuccessWitness (r : Fin m) (hr : r ∈ successfulRoots) :
      ∃ u : List ℕ, u.length = ell ∧ surviveAlong (field r) [] u ∧
        Spine.pathHistory realPotential ell 0 (field r) u ∈ corridor := by
    change r ∈ Finset.univ.filter (fun r =>
      field r ∈ hasPathHistoryIn (ι := ℕ) realPotential ell 0 corridor) at hr
    exact (Finset.mem_filter.mp hr).2
  let chosenAddress : ∀ r : Fin m, r ∈ successfulRoots → List ℕ :=
    fun r hr => Classical.choose (hsuccessWitness r hr)
  have chosenAddress_spec (r : Fin m) (hr : r ∈ successfulRoots) :
      (chosenAddress r hr).length = ell ∧
        surviveAlong (field r) [] (chosenAddress r hr) ∧
        Spine.pathHistory realPotential ell 0 (field r)
            (chosenAddress r hr) ∈ corridor :=
    Classical.choose_spec (hsuccessWitness r hr)
  let embed : {r // r ∈ successfulRoots} → RootIndexed.TreeNode (Fin m) ℕ :=
    fun r => (r.1, chosenAddress r.1 r.2)
  have hembed_mem (r : {r // r ∈ successfulRoots}) : embed r ∈ actual := by
    have hspec := chosenAddress_spec r.1 r.2
    have hroot : (r.1, ([] : List ℕ)) ∈ initial := by
      simp [initial, RootIndexed.mem_initialPopulation_iff]
    have hparticle : embed r ∈ population ell field := by
      apply ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_of_path
        (initialPosition := fun _ : Fin m => 0) (d := id) (hd := measurable_id) (initial := initial)
        (hinitialDepth := hinitialDepth) (cutoff := ell) (n := ell)
        (window := window)
        (hwindow := measurableSet_positiveARestartedWindow
          ell ellN logN b v c κ)
        (upper := upper)
        (hupper := positiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
        (field := field) (r := r.1) (u := chosenAddress r.1 r.2)
      · exact hspec.1
      · exact hroot
      · exact hspec.2.1
      · intro v hv
        exact hweight r.1 v
      · intro k hk
        exact positiveA_corridorPath_mem_restartedWindow
          ell ellN logN b v c κ field r.1 (chosenAddress r.1 r.2)
          hspec.1 hspec.2.2 k hk
    exact (populationFinite.mem_toFinset ell field (embed r)).mpr hparticle
  have hinjective : Set.InjOn embed (↑successfulRoots.attach : Set {r // r ∈ successfulRoots}) := by
    intro r _ s _ hrs
    apply Subtype.ext
    exact congrArg Prod.fst hrs
  have hcardImage : (successfulRoots.attach.image embed).card = successfulRoots.card := by
    rw [Finset.card_image_iff.mpr hinjective]
    simp
  have himageSubset : successfulRoots.attach.image embed ⊆ actual := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact hembed_mem r
  calc
    successfulRoots.card = (successfulRoots.attach.image embed).card :=
      hcardImage.symm
    _ ≤ actual.card := Finset.card_le_card himageSubset

/-- Boundary normalization makes the pathwise successful-root embedding hold
almost surely on the pre-sampled finite-root environment. -/
lemma ae_positiveA_successfulRoots_card_le_killedPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      let successfulRoots :=
        positiveASuccessfulRoots m ell logN b v field
      let initial := RootIndexed.initialPopulation (α := ℕ)
        (Finset.univ : Finset (Fin m))
      let window := positiveARestartedWindow ell ellN logN b v c κ
      let upper := positiveAWindowUpper ell ellN logN b v c κ
      let populationFinite :=
        RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
          (fun _ : Fin m => 0) id measurable_id initial
          (by simp [initial, RootIndexed.mem_initialPopulation_iff])
          ell window (measurableSet_positiveARestartedWindow
            ell ellN logN b v c κ)
          upper (positiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)
      successfulRoots.card ≤ (populationFinite.toFinset ell field).card := by
  filter_upwards
    [RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots
      (μ := μ) hboundary (Finset.univ : Finset (Fin m))]
    with field hweight
  exact positiveA_successfulRoots_card_le_killedPopulation
    m ell ellN logN b v c κ field
    (fun r u => hweight r (Finset.mem_univ r) u)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

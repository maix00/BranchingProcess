/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.RightTailKilledCapacity
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
import Probability.BranchingRandomWalk.Population.Processes.Causal.PathWindow

/-!
# Embedding first-stage corridor successes into the killed population

Every successful initial root supplies a distinct generation-`ell` particle
in the actual restarted-window population.  This is the pathwise bridge from
the independent-root count to the second stage of the right-tail argument.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- A generation-`n` path whose prefixes satisfy the prescribed windows and
whose ancestral offspring weights are finite is retained by the restarted
real-position population. -/
theorem mem_ofRestartedRealPositionSets_of_path
    {Root : Type*}
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    (initialPosition : Root → ℝ) (initial : Finset (RootIndexed.TreeNode Root ℕ))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff n : ℕ) (window : ℕ → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) (upper : ℕ → ℝ)
    (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField Root ℕ ℝ) (r : Root) (u : List ℕ)
    (hu : u.length = n)
    (hroot : (r, []) ∈ initial)
    (hsurvive : surviveAlong (field r) [] u)
    (hweight : ∀ v, v.length < n →
      totalPotentialWeight realPotential (-1) (field r v) ≠ ∞)
    (hwindowPath : ∀ k ≤ n,
      RootIndexed.relativePositionAtGeneration initialPosition id
        (restartAnchor cutoff k) k (r, u.take k) field ∈ window k) :
    (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      initialPosition id measurable_id initial hinitialDepth cutoff window
      hwindow upper hupper n field := by
  classical
  let potential : Potential ℝ := realPotential
  let keep : ℕ → RootIndexed.StepField Root ℕ ℝ →
      RootIndexed.TreeNode Root ℕ → Prop := fun k sample q =>
    (k = 0 ∨ q.2.length ≠ k ∨
      totalPotentialWeight potential (-1)
        (sample (parent q).1 (parent q).2) ≠ ∞) ∧
      RootIndexed.relativePositionAtGeneration initialPosition id
        (restartAnchor cutoff k) k q sample ∈ window k
  let finite : ∀ (k : ℕ) (parents : Finset (RootIndexed.TreeNode Root ℕ))
      (sample : RootIndexed.StepField Root ℕ ℝ),
      {q | q ∈ RootIndexed.childrenAtGeneration k parents sample ∧
        keep (k + 1) sample q}.Finite := by
    intro k parents sample
    let goodParents := parents.filter fun p =>
      totalPotentialWeight potential (-1) (sample p.1 p.2) ≠ ∞
    have hfinite :
        {q | q ∈ RootIndexed.childrenAtGeneration k goodParents sample ∧
          RootIndexed.relativePositionAtGeneration initialPosition id
            (restartAnchor cutoff (k + 1)) (k + 1) q sample ∈
              window (k + 1)}.Finite := by
      apply RootIndexed.childrenAtGeneration_filter_finite_of_upperBound
        k goodParents sample
        (fun q => RootIndexed.relativePositionAtGeneration initialPosition id
          (restartAnchor cutoff (k + 1)) (k + 1) q sample)
        (window (k + 1)) (upper (k + 1)) (hupper (k + 1))
      intro p hp hpdepth a
      have hpweight : totalPotentialWeight potential (-1)
          (sample p.1 p.2) ≠ ∞ := (Finset.mem_filter.mp hp).2
      let parentRelative := RootIndexed.relativePositionAtGeneration
        initialPosition id (restartAnchor cutoff (k + 1)) k p sample
      have hstep := finite_realized_children_potential_below
        (φ := potential) (sample p.1 p.2) hpweight (a - parentRelative)
      apply hstep.subset
      intro j hj
      refine ⟨hj.1, ?_⟩
      have hpotential :
          (sample p.1 p.2).potentialValue' potential j =
            value' ((sample p.1 p.2).map id) j := by
        cases hslot : sample p.1 p.2 j <;>
          simp [Step.map, value', Step.potentialValue', Step.potentialAt?,
            potential, hslot]
      rw [hpotential]
      apply le_sub_iff_add_le.mpr
      rw [add_comm]
      rw [← RootIndexed.relativePositionAtGeneration_child initialPosition id
        sample (restartAnchor_succ_le_parent cutoff k) p hpdepth j]
      exact hj.2
    apply hfinite.subset
    intro q hq
    obtain ⟨p, hp, hpdepth, j, hj, rfl⟩ :=
      (RootIndexed.mem_childrenAtGeneration_iff k parents sample q).mp hq.1
    have hpweight : totalPotentialWeight potential (-1)
        (sample p.1 p.2) ≠ ∞ := by
      have hguard := hq.2.1
      simp [hpdepth] at hguard
      exact hguard
    refine ⟨RootIndexed.childAddress_mem_childrenAtGeneration k goodParents
      sample p (Finset.mem_filter.mpr ⟨hp, hpweight⟩) hpdepth j hj, ?_⟩
    exact hq.2.2
  change (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      initialPosition id measurable_id initial hinitialDepth cutoff window
      hwindow upper hupper n field
  induction n generalizing u with
  | zero =>
      have hu0 : u = [] := List.eq_nil_of_length_eq_zero hu
      subst u
      change (r, []) ∈ initial
      exact hroot
  | succ n ih =>
      have hne : u ≠ [] := by
        intro hu'
        simp [hu'] at hu
      let i : ℕ := u.getLast hne
      let v : List ℕ := u.dropLast
      have happend : u = v ++ [i] := by
        dsimp [v, i]
        exact (List.dropLast_append_getLast hne).symm
      have hvlen : v.length = n := by
        dsimp [v]
        rw [List.length_dropLast, hu]
        omega
      have hsurviveSplit : surviveAlong (field r) [] v ∧
          survive (field r v) i := by
        rw [happend] at hsurvive
        exact (surviveAlong_append_singleton (field r) [] v i).mp hsurvive
      have hwindowParent : ∀ k ≤ n,
          RootIndexed.relativePositionAtGeneration initialPosition id
            (restartAnchor cutoff k) k (r, v.take k) field ∈ window k := by
        intro k hk
        have hk' : k ≤ n + 1 := by omega
        have htake : u.take k = v.take k := by
          rw [happend]
          exact List.take_append_of_le_length (by simpa [v, hvlen] using hk)
        rw [← htake]
        exact hwindowPath k hk'
      have hweightParent : ∀ w, w.length < n →
          totalPotentialWeight potential (-1) (field r w) ≠ ∞ := by
        intro w hw
        exact hweight w (by omega)
      have hparent : (r, v) ∈
          RootIndexed.CausalPopulation.ofRestartedRealPositionSets
            initialPosition id measurable_id initial hinitialDepth cutoff
            window hwindow upper hupper n field := by
        exact ih v hvlen hsurviveSplit.1 hweightParent hwindowParent
      have hparentSelected : (r, v) ∈
          RootIndexed.CausalPopulation.selectedBy initial keep finite n field := by
        change (r, v) ∈
          RootIndexed.CausalPopulation.selectedBy initial keep finite n field at hparent
        exact hparent
      change (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
        initialPosition id measurable_id initial hinitialDepth cutoff window
        hwindow upper hupper (n + 1) field
      change (r, u) ∈ RootIndexed.CausalPopulation.selectedBy
        initial keep finite (n + 1) field
      rw [RootIndexed.CausalPopulation.mem_selectedBy_succ
        (initial := initial) (keep := keep) (hfinite := finite)
        (n := n) (field := field) (q := (r, u))]
      refine ⟨?_, ?_⟩
      · exact (RootIndexed.mem_childrenAtGeneration_iff n
          (RootIndexed.CausalPopulation.selectedBy initial keep finite n field)
          field (r, u)).2
          ⟨(r, v), hparentSelected, hvlen, i, hsurviveSplit.2,
            congrArg (fun address => (r, address)) happend⟩
      · refine ⟨?_, ?_⟩
        · right
          right
          simpa [potential, parent, happend, hu] using
            hweight v (by rw [hvlen]; exact Nat.lt_succ_self n)
        · have htakeEnd : u.take (n + 1) = u :=
            List.take_of_length_le (Nat.le_of_eq hu)
          simpa [htakeEnd] using hwindowPath (n + 1) (Nat.le_refl _)

/-- The first-stage affine corridor is exactly the root-relative part of the
restarted schedule through the cutoff. -/
theorem rightTailPositiveA_corridorPath_mem_restartedWindow
    {Root : Type*} (ell ellN : ℕ) (logN b v c κ : ℝ)
    (field : RootIndexed.StepField Root ℕ ℝ) (r : Root)
    (u : List ℕ) (hu : u.length = ell)
    (hcorridor : Spine.pathHistory realPotential ell 0 (field r) u ∈
      affineCorridorThrough ell (-b * logN) 0 (b * logN)
        ((-b + v) * logN)) :
    ∀ k ≤ ell,
      RootIndexed.relativePositionAtGeneration (fun _ : Root => 0) id
        (restartAnchor ell k) k (r, u.take k) field ∈
          rightTailPositiveARestartedWindow ell ellN logN b v c κ k := by
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
    simpa [rightTailPositiveARestartedWindow, hkle] using hbounds
  · have hkeq : k = ell := by omega
    subst k
    have hbounds :
        -b * logN ≤ Spine.pathHistory realPotential ell 0 (field r) u j ∧
          Spine.pathHistory realPotential ell 0 (field r) u j ≤
            (-b + v) * logN := by
      constructor
      · simpa [j, mul_zero, mul_comm] using hcoord.1
      · simpa [j, mul_zero, mul_comm] using hcorridor.2
    simpa [rightTailPositiveARestartedWindow] using hbounds

/-- Distinct successful initial root labels produce distinct particles in the
actual generation-`ell` restarted killed population. -/
noncomputable def rightTailPositiveASuccessfulRoots
    (m ell : ℕ) (logN b v : ℝ)
    (field : RootIndexed.StepField (Fin m) ℕ ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun r =>
    field r ∈ hasPathHistoryIn (ι := ℕ) realPotential ell 0
      (affineCorridorThrough ell (-b * logN) 0 (b * logN)
        ((-b + v) * logN))

theorem rightTailPositiveA_successfulRoots_card_le_killedPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RootIndexed.StepField (Fin m) ℕ ℝ)
    (hweight : ∀ r u,
      totalPotentialWeight realPotential (-1) (field r u) ≠ ∞) :
    let successfulRoots := rightTailPositiveASuccessfulRoots
      m ell logN b v field
    let initial := RootIndexed.initialPopulation (α := ℕ)
      (Finset.univ : Finset (Fin m))
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let populationFinite :=
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
        (fun _ : Fin m => 0) id measurable_id initial
        (by simp [initial, RootIndexed.mem_initialPopulation_iff])
        ell window (measurableSet_rightTailPositiveARestartedWindow
          ell ellN logN b v c κ)
        upper (rightTailPositiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
    successfulRoots.card ≤ (populationFinite.toFinset ell field).card := by
  classical
  let corridor := affineCorridorThrough ell (-b * logN) 0
    (b * logN) ((-b + v) * logN)
  let successfulRoots : Finset (Fin m) :=
    rightTailPositiveASuccessfulRoots m ell logN b v field
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  let population := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell window
    (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    upper (rightTailPositiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  have populationFinite : population.FiniteSlices := by
    dsimp [population]
    exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
      (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
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
      apply mem_ofRestartedRealPositionSets_of_path
        (initialPosition := fun _ : Fin m => 0) (initial := initial)
        (hinitialDepth := hinitialDepth) (cutoff := ell) (n := ell)
        (window := window)
        (hwindow := measurableSet_rightTailPositiveARestartedWindow
          ell ellN logN b v c κ)
        (upper := upper)
        (hupper := rightTailPositiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
        (field := field) (r := r.1) (u := chosenAddress r.1 r.2)
      · exact hspec.1
      · exact hroot
      · exact hspec.2.1
      · intro v hv
        exact hweight r.1 v
      · intro k hk
        exact rightTailPositiveA_corridorPath_mem_restartedWindow
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
theorem ae_rightTailPositiveA_successfulRoots_card_le_killedPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      let successfulRoots :=
        rightTailPositiveASuccessfulRoots m ell logN b v field
      let initial := RootIndexed.initialPopulation (α := ℕ)
        (Finset.univ : Finset (Fin m))
      let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
      let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
      let populationFinite :=
        RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
          (fun _ : Fin m => 0) id measurable_id initial
          (by simp [initial, RootIndexed.mem_initialPopulation_iff])
          ell window (measurableSet_rightTailPositiveARestartedWindow
            ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)
      successfulRoots.card ≤ (populationFinite.toFinset ell field).card := by
  filter_upwards
    [RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots
      (μ := μ) hboundary (Finset.univ : Finset (Fin m))]
    with field hweight
  exact rightTailPositiveA_successfulRoots_card_le_killedPopulation
    m ell ellN logN b v c κ field
    (fun r u => hweight r (Finset.mem_univ r) u)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

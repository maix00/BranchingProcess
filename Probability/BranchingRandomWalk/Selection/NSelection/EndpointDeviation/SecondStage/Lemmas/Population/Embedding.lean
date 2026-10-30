/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Window
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Large
import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.TubeParameters
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Probability.Process.Path.Restart.Basic

/-!
# Second-stage corridor paths in the restarted killed population

## Internal proof declarations


The proof-chain lemma used in `SecondStage/Lemmas/Population/Transfer.lean`,
`mem_restartedPopulation_of_secondStageCorridor`, is the concatenation rule
\[
  (r,u)\in\mathcal P_\ell,\quad
  \operatorname{survive}(r,u,w),\quad
  \operatorname{path}(r,u,w)\in\mathcal C_{\ell_N-\ell}
  \quad\Longrightarrow\quad
  (r,u\mathbin{+\!+}w)\in\mathcal P_{\ell_N},
\]
under the stated finite-weight condition. Here $\mathcal P_j$ is the
restarted killed population and $\mathcal C_j$ is the second-stage corridor.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.Process.Path

/-- If a retained particle at the restart generation has a surviving subtree
path in the second-stage affine corridor, the concatenated path is retained
at the terminal generation.  `hweight` is the finite-weight condition used
by the totalized killed process; under the boundary normalization it
holds simultaneously at all addresses almost surely. -/
lemma mem_restartedPopulation_of_secondStageCorridor
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    (hell : 0 < ell) (hellN : ell ≤ ellN)
    (hstart : 0 ≤ b * logN)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RootIndexed.StepField (Fin m) ℕ ℝ)
    (r : Fin m) (u w : List ℕ)
    (hu : u.length = ell) (hw : w.length = ellN - ell)
    (hq : (r, u) ∈
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets
        (fun _ : Fin m => 0) id measurable_id
        (RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)))
        (by intro p hp; rcases RootIndexed.mem_initialPopulation_iff.mp hp with
          ⟨root, -, rfl⟩; simp)
        ell (positiveARestartedWindow ell ellN logN b v c κ)
        (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
        (positiveAWindowUpper ell ellN logN b v c κ)
        (positiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
        ell field)
    (hsurvive : surviveAlong
      (RootIndexed.subtreeStepFieldVector
        (fun _ : Unit => (r, u)) field ()) [] w)
    (hcorridor : Spine.pathHistory realPotential (ellN - ell) 0
      (RootIndexed.subtreeStepFieldVector
        (fun _ : Unit => (r, u)) field ()) w ∈
      positiveASecondStageCorridor (ellN - ell) κ c v)
    (hweight : ∀ z : List ℕ,
      z.length < ellN →
        totalPotentialWeight realPotential (-1) (field r z) ≠ ∞) :
    (r, u ++ w) ∈
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets
        (fun _ : Fin m => 0) id measurable_id
        (RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)))
        (by intro p hp; rcases RootIndexed.mem_initialPopulation_iff.mp hp with
          ⟨root, -, rfl⟩; simp)
        ell (positiveARestartedWindow ell ellN logN b v c κ)
        (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
        (positiveAWindowUpper ell ellN logN b v c κ)
        (positiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ)
        ellN field := by
  classical
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  let window := positiveARestartedWindow ell ellN logN b v c κ
  let upper := positiveAWindowUpper ell ellN logN b v c κ
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨root, -, rfl⟩
    simp
  let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell window
    (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  have hqP : (r, u) ∈ P ell field := by
    simpa [P, initial, window, upper, hinitialDepth] using hq
  have hroot : (r, ([] : List ℕ)) ∈ initial := by
    simp [initial, RootIndexed.mem_initialPopulation_iff]
  have hsurvivePrefix : surviveAlong (field r) [] u :=
    P.surviveAlong_of_mem hqP
  have hsurviveSuffix : surviveAlong (field r) u w := by
    have hlocal : surviveAlong
        (fun z => field r (u ++ z)) [] w := by
      change surviveAlong
        (RootIndexed.subtreeStepFieldVector
          (fun _ : Unit => (r, u)) field ()) [] w at hsurvive
      exact hsurvive
    simpa using (surviveAlong_rebase (field r) u [] w).mp hlocal
  have hsurvivePath : surviveAlong (field r) [] (u ++ w) :=
    (surviveAlong_append (field r) [] u w).mpr
      ⟨hsurvivePrefix, hsurviveSuffix⟩
  have hwindowPath : ∀ k ≤ ellN,
      RootIndexed.relativePositionAtGeneration (fun _ : Fin m => 0) id
        (restartAnchor ell k) k (r, (u ++ w).take k) field ∈ window k := by
    intro k hk
    by_cases hkle : k ≤ ell
    · by_cases hkzero : k = 0
      · subst k
        simp [RootIndexed.relativePositionAtGeneration,
          RootIndexed.positionAtGeneration, window,
          positiveARestartedWindow,
          hell, hstart]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
        have hprefixWindow :=
          RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_all_windows
            (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
            window (measurableSet_positiveARestartedWindow
              ell ellN logN b v c κ)
            upper (positiveARestartedWindow_subset_Iic_upper
              ell ellN logN b v c κ) hqP hkpos hkle
        have htake : (u ++ w).take k = u.take k := by
          rw [List.take_append_of_le_length (by simpa [hu] using hkle)]
        have hprefixWindow' :
            RootIndexed.relativePositionAtGeneration (fun _ : Fin m => 0) id
              (restartAnchor ell k) k (r, u.take k) field ∈ window k := by
          simpa [P, initial, window, upper, hinitialDepth] using hprefixWindow
        simpa [htake] using hprefixWindow'
    · have hkgt : ell < k := by omega
      let j : ℕ := k - ell
      have hjpos : 0 < j := by dsimp [j]; omega
      have hjle : j ≤ ellN - ell := by dsimp [j]; omega
      have htake : (u ++ w).take k = u ++ w.take j := by
        dsimp [j]
        rw [List.take_append]
        have hfirst : u.take k = u := List.take_of_length_le (by omega)
        have htail : k - u.length = j := by simp [j, hu]
        rw [hfirst, htail]
      let subtree := RootIndexed.subtreeStepFieldVector
        (fun _ : Unit => (r, u)) field ()
      have hlocalPosition :=
        pathPotential_subtreeStepFieldVector_eq_position_sub
          (φ := realPotential) field r u (w.take j)
      have htakeParent : (u ++ w).take ell = u := by
        rw [List.take_append_of_le_length (l₁ := u) (l₂ := w)
          (i := ell) (by simp [hu])]
        simp [hu]
      have hrelative :
          RootIndexed.relativePositionAtGeneration (fun _ : Fin m => 0) id
              (restartAnchor ell k) k (r, (u ++ w).take k) field =
            Spine.pathHistory realPotential (ellN - ell) 0 subtree w
              ⟨j, Nat.lt_succ_of_le hjle⟩ := by
        rw [RootIndexed.relativePositionAtGeneration,
          restartAnchor_eq_cutoff hkgt]
        have hdepthK : ((u ++ w).take k).length = k := by
          have htotal : ell + (ellN - ell) = ellN := Nat.add_sub_of_le hellN
          simp [List.length_take, List.length_append, hu, hw,
            Nat.min_eq_left hk, htotal]
        rw [htake]
        have hanchorTake : (u ++ w.take j).take ell = u := by
          rw [List.take_append_of_le_length (l₁ := u) (l₂ := w.take j)
            (i := ell) (by simp [hu])]
          simp [hu]
        rw [hanchorTake]
        have hdepthK' : (u ++ w.take j).length = k := by
          rw [← htake]
          exact hdepthK
        simp [RootIndexed.positionAtGeneration, hdepthK', hu]
        calc
          RootIndexed.position (fun _ : Fin m => 0) id field r
              (u ++ w.take j) -
              RootIndexed.position (fun _ : Fin m => 0) id field r u =
              Spine.pathPotential realPotential subtree (w.take j) := by
            simpa [RootIndexed.position, RootIndexed.displace,
              Spine.pathPotential, realPotential, subtree] using hlocalPosition.symm
          _ = Spine.pathHistory realPotential (ellN - ell) 0 subtree w
              ⟨j, Nat.lt_succ_of_le hjle⟩ := by
            simp [Spine.pathHistory]
      have hcorridorBounds := hcorridor.1 ⟨j, Nat.lt_succ_of_le hjle⟩
      by_cases hterminal : k = ellN
      · have hjD : j = ellN - ell := by dsimp [j]; omega
        have hellNgt : ell < ellN := by omega
        have hellNne : ellN ≠ ell := ne_of_gt hellNgt
        have hterm := hcorridor.2
        have hbounds :
            positiveADrift ell ellN κ c j ≤
                Spine.pathHistory realPotential (ellN - ell) 0 subtree w
                  ⟨j, Nat.lt_succ_of_le hjle⟩ ∧
              Spine.pathHistory realPotential (ellN - ell) 0 subtree w
                  ⟨j, Nat.lt_succ_of_le hjle⟩ ≤
                positiveADrift ell ellN κ c j +
                  v * (((ellN - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
          constructor
          · simpa [positiveASecondStageCorridor, affineCorridorThrough,
              positiveASecondStageSlope, positiveADrift,
              hjD, subtree] using hcorridorBounds.1
          · simpa [positiveASecondStageCorridor, affineCorridorThrough,
              positiveASecondStageSlope, positiveADrift,
              hjD, subtree] using hterm
        have hknotlt : ¬ k < ellN := by omega
        have hEllNnotLt : ¬ ellN < ell := by omega
        rw [hrelative]
        simpa [window, positiveARestartedWindow, hellNgt,
          hellNne, hterminal, hknotlt, hEllNnotLt, hjD] using hbounds
      · have hjlt : j < ellN - ell := by dsimp [j]; omega
        have hklt : k < ellN := by omega
        have hnotltEll : ¬ k < ell := by omega
        have hkneEll : k ≠ ell := by omega
        have hbounds :
            positiveADrift ell ellN κ c j ≤
                Spine.pathHistory realPotential (ellN - ell) 0 subtree w
                  ⟨j, Nat.lt_succ_of_le hjle⟩ ∧
              Spine.pathHistory realPotential (ellN - ell) 0 subtree w
                  ⟨j, Nat.lt_succ_of_le hjle⟩ ≤
                positiveADrift ell ellN κ c j +
                  c * (((ellN - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 3)) := by
          simpa [positiveASecondStageCorridor, affineCorridorThrough,
            positiveASecondStageSlope,
            positiveASecondStageWidth, positiveADrift,
            hjlt, subtree] using hcorridorBounds
        rw [hrelative]
        simpa [window, positiveARestartedWindow,
          positiveADrift, j, hjlt, hklt, hnotltEll, hkneEll,
          subtree] using hbounds
  have hweight' : ∀ z : List ℕ, z.length < ellN →
      totalPotentialWeight realPotential (-1) (field r z) ≠ ∞ := hweight
  have hresult := ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_of_path
    (initialPosition := fun _ : Fin m => 0) (d := id) (hd := measurable_id) (initial := initial)
    (hinitialDepth := hinitialDepth) (cutoff := ell) (n := ellN)
    (window := window)
    (hwindow := measurableSet_positiveARestartedWindow
      ell ellN logN b v c κ)
    (upper := upper)
    (hupper := positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
    (field := field) (r := r) (u := u ++ w)
  have hlen : (u ++ w).length = ellN := by
    simp [hu, hw, Nat.add_sub_of_le hellN]
  exact hresult hlen hroot hsurvivePath hweight' hwindowPath

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

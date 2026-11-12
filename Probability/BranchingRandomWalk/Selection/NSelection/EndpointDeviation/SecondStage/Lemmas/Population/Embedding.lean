/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Population.Processes.Causal.Path.Window
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Coupling
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Large
import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.Position
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.TubeParameters
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.ParameterBounds
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
import Probability.Process.Path.Restart.Basic

/-!
# Second-stage corridor paths in the restarted selected BRW population

## Internal proof declarations

* `mem_restartedPopulation_of_secondStageCorridor` proves that a retained
  particle at generation $\ell$ with a surviving continuation in the second
  corridor remains in the restarted selected BRW population at generation
  $\ell_N$.
* `positiveASelectedBRW_terminal_position_lt` proves that every particle in the
  restarted selected BRW population at generation $\ell_N$ has position below
  $(-b+v)\log N+(\kappa/c^2+v)(\ell_N-\ell)^{1/3}$.
* `positiveASelectedBRW_endpointHigh_implies_terminalEmpty_or_capacityFailure_ae`
  proves the almost-sure implication
  \[
    \{M_{\ell_N}\ge x\}\subseteq
      \{\mathcal P_{\ell_N}=\varnothing\}\cup
      \{\text{capacity fails before }\ell_N\}.
  \]
* `measure_firstN_endpointHigh_le_terminalEmpty_add_capacityFailure`
  transfers this implication to finite-root probabilities:
  \[
    \mathbb P(M_{\ell_N}\ge x)\le
      \mathbb P(\mathcal P_{\ell_N}=\varnothing)+
      \mathbb P(\text{capacity fails before }\ell_N).
  \]

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
restarted selected BRW population and $\mathcal C_j$ is the second-stage corridor.

The terminal-position lemma below bounds every retained endpoint by the
cutoff upper boundary plus the terminal relative-position upper boundary.
The endpoint coupling step combines this strict bound with the capacity
coupling for the restarted selected BRW population to obtain
\[
 \{M_{\ell_N}\ge x\}\subseteq
 \{\mathcal P_{\ell_N}=\varnothing\}\cup
 \{\text{the selected BRW population exceeds capacity before }\ell_N\}
\]
up to a null set.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Coupling
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.Process.Path

/-- If a retained particle at the restart generation has a surviving subtree
path in the second-stage affine corridor, the concatenated path is retained
at the terminal generation.  `hweight` is the finite-weight condition used
by the totalized selected BRW process; under the boundary normalization it
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

/-- The first-stage cutoff position plus the terminal relative tube bound
controls every particle retained at the terminal generation. -/
lemma positiveASelectedBRW_terminal_position_lt
    (m ell ellN : ℕ) (logN b v c κ threshold : ℝ)
    (hell : 0 < ell) (hellN : ell < ellN) (hκ : 0 ≤ κ)
    (hthreshold : (-b + v) * logN +
      (κ / c ^ 2 + v) * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) < threshold)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RootIndexed.StepField (Fin m) ℕ ℝ)
    (q : RootIndexed.TreeNode (Fin m) ℕ)
    (hq : q ∈ positiveASelectedBRWPopulation m ell ellN logN b v c κ ellN field) :
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 < threshold := by
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  let window := positiveARestartedWindow ell ellN logN b v c κ
  let upper := positiveAWindowUpper ell ellN logN b v c κ
  let population := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => (0 : ℝ)) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  have hq' : q ∈ population ellN field := by
    simpa [population, positiveASelectedBRWPopulation, initial, window, upper,
      hinitialDepth] using hq
  have hdepth : q.2.length = ellN := population.depth ellN field q hq'
  have htakeEndpoint : q.2.take ellN = q.2 :=
    List.take_of_length_le (le_of_eq hdepth)
  have hprefixLength : (q.2.take ell).length = ell := by
    simp [List.length_take, hdepth, Nat.min_eq_left (Nat.le_of_lt hellN)]
  have hcutoffWindow :=
    RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_all_windows
      (fun _ : Fin m => (0 : ℝ)) id measurable_id initial hinitialDepth ell
      window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
      upper (positiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ) hq' hell (Nat.le_of_lt hellN)
  have hterminalWindow :=
    RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_all_windows
      (fun _ : Fin m => (0 : ℝ)) id measurable_id initial hinitialDepth ell
      window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
      upper (positiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ) hq' (Nat.zero_lt_of_lt hellN) le_rfl
  have hterminalRelativeEq :
      RootIndexed.relativePositionAtGeneration (fun _ : Fin m => (0 : ℝ)) id
          (restartAnchor ell ellN) ellN (q.1, q.2.take ellN) field =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
            q.1 (q.2.take ell) := by
    simp [RootIndexed.relativePositionAtGeneration,
      RootIndexed.positionAtGeneration, restartAnchor_eq_cutoff hellN,
      hdepth, htakeEndpoint, hprefixLength]
  have hcutoffBounds :
      -b * logN ≤ RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
          q.1 (q.2.take ell) ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
          q.1 (q.2.take ell) ≤ (-b + v) * logN := by
    simpa [RootIndexed.relativePositionAtGeneration,
      RootIndexed.positionAtGeneration, positiveARestartedWindow,
      window, hprefixLength] using hcutoffWindow
  rw [hterminalRelativeEq] at hterminalWindow
  have hterminalBounds :
      positiveADrift ell ellN κ c (ellN - ell) ≤
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 -
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
              q.1 (q.2.take ell) ∧
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 -
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
              q.1 (q.2.take ell) ≤
          positiveADrift ell ellN κ c (ellN - ell) +
            v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
    simpa [positiveARestartedWindow, window,
      not_lt_of_ge (le_of_lt hellN), ne_of_gt hellN] using hterminalWindow
  have hdecomposition :
      RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
          q.1 (q.2.take ell) +
        (RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
            q.1 (q.2.take ell)) := by
    ring
  have hdrift := positiveADrift_le_span ell ellN (ellN - ell) κ c
    hellN hκ (by omega)
  calc
    RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 =
        RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
          q.1 (q.2.take ell) +
        (RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field q.1 q.2 -
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id field
            q.1 (q.2.take ell)) := hdecomposition
    _ ≤ (-b + v) * logN +
          (positiveADrift ell ellN κ c (ellN - ell) +
            v * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) :=
      add_le_add hcutoffBounds.2 hterminalBounds.2
    _ ≤ (-b + v) * logN +
          (κ / c ^ 2 + v) * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
      nlinarith [hdrift]
    _ < threshold := hthreshold

/-- A large first-`N` endpoint minimum forces either extinction of the
restarted selected BRW population or failure of its finite-horizon capacity bound.
The implication follows from slice domination of the selected selected BRW
population by the rank-installed first-`N` BRW population on the capacity
event and the strict terminal-position bound. -/
lemma positiveASelectedBRW_endpointHigh_implies_terminalEmpty_or_capacityFailure_ae
    (m N ell ellN : ℕ) (logN b v c κ threshold : ℝ)
    (hell : 0 < ell) (hellN : ell < ellN) (hκ : 0 ≤ κ)
    (hthreshold : (-b + v) * logN +
      (κ / c ^ 2 + v) * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) < threshold)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Fin m ⊕ Fin m) μ,
      threshold ≤ firstNSelectedEndpointMinimum m N ellN
        (letI : DecidableEq (RootIndexed.TreeNode (Fin m) ℕ) :=
          fun a b => LinearOrder.toDecidableEq a b;
         RootIndexed.restartedRealPositionNSelectedBRWField N
          (Finset.univ : Finset (Fin m)) (fun _ => 0) id
          (RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices
            (fun _ : Fin m => 0) id measurable_id
            (RootIndexed.initialPopulation (α := ℕ)
              (Finset.univ : Finset (Fin m)))
            (by
              intro p hp
              rcases RootIndexed.mem_initialPopulation_iff.mp hp with
                ⟨r, _hr, rfl⟩
              simp)
            ell (positiveARestartedWindow ell ellN logN b v c κ)
            (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
            (positiveAWindowUpper ell ellN logN b v c κ)
            (positiveARestartedWindow_subset_Iic_upper
              ell ellN logN b v c κ)).toFinset ellN field) →
      (¬ (positiveASelectedBRWPopulation m ell ellN logN b v c κ ellN
          (RootIndexed.StepField.left field)).Nonempty ∨
        RootIndexed.StepField.left field ∈
          ((positiveASelectedBRWPopulation m ell ellN logN b v c κ).capacityEvent
            N ellN)ᶜ) := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode (Fin m) ℕ) :=
    fun a b => LinearOrder.toDecidableEq a b
  let roots : Finset (Fin m) := Finset.univ
  let initial := RootIndexed.initialPopulation (α := ℕ) roots
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  let window := positiveARestartedWindow ell ellN logN b v c κ
  let upper := positiveAWindowUpper ell ellN logN b v c κ
  let selectedBRWPopulation := RootIndexed.restartedRealPositionSelectedBRWPopulation
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let selectedBRWPopulationFiniteSlices := RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let selectedBRWPopulationSlice := RootIndexed.restartedRealPositionSelectedBRWPopulationSlice
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let nSelectedBRWField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
    (fun _ : Fin m => 0) id selectedBRWPopulationSlice ellN
  let selectedBRWPopulationOnRestartedField :=
    positiveASelectedBRWPopulation m ell ellN logN b v c κ
  have hselectedBRWPopulationSetEq (k : ℕ)
      (field : RootIndexed.StepField (Fin m ⊕ Fin m) ℕ ℝ) :
      selectedBRWPopulation k field = selectedBRWPopulationOnRestartedField k
        (RootIndexed.StepField.left field) := by
    dsimp [selectedBRWPopulation, selectedBRWPopulationOnRestartedField,
      roots, initial, window, upper,
      RootIndexed.restartedRealPositionSelectedBRWPopulation,
      RootIndexed.CausalPopulation.pullback_population,
        positiveASelectedBRWPopulation]
    congr 1
  have hselectedBRWPopulationSliceSetEq (field : RootIndexed.StepField (Fin m ⊕ Fin m) ℕ ℝ) :
      (selectedBRWPopulationSlice ellN field : Set (RootIndexed.TreeNode (Fin m) ℕ)) =
        selectedBRWPopulationOnRestartedField ellN
          (RootIndexed.StepField.left field) := by
    change (selectedBRWPopulationFiniteSlices.toFinset ellN field :
      Set (RootIndexed.TreeNode (Fin m) ℕ)) = _
    rw [selectedBRWPopulationFiniteSlices.coe_toFinset, hselectedBRWPopulationSetEq ellN field]
  have hselectedBRWPopulationCapacityEq
      (field : RootIndexed.StepField (Fin m ⊕ Fin m) ℕ ℝ) :
      field ∈ selectedBRWPopulation.capacityEvent N ellN ↔
        RootIndexed.StepField.left field ∈
          selectedBRWPopulationOnRestartedField.capacityEvent N ellN := by
    simp only [RootIndexed.CausalPopulation.capacityEvent, Set.mem_iInter,
      Set.mem_ofPred_eq]
    constructor
    · intro h k
      have hk := h k
      simpa only [hselectedBRWPopulationSetEq k.1 field] using hk
    · intro h k
      have hk := h k
      simpa only [hselectedBRWPopulationSetEq k.1 field] using hk
  have hcoupled := RootIndexed.restartedRealPositionCoupledInjectionOnRoots_ae
    μ hboundary N roots (fun _ => 0) ell window
    (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ) ellN
  have hcoupled' : ∀ᵐ field ∂RootIndexed.stepFieldLaw
      (Root := Fin m ⊕ Fin m) μ,
      field ∈ selectedBRWPopulation.capacityEvent N ellN →
        Nonempty (Cloud.SliceDominatingMap id
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField (fun _ : Fin m => 0)
              (RootIndexed.StepField.left field))
            (selectedBRWPopulationSlice ellN field))
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            (RootIndexed.BranchingWalk.ofStepField (fun _ : Fin m => 0)
              (RootIndexed.restartedRealPositionNSelectedBRWField N roots
              (fun _ : Fin m => 0) id selectedBRWPopulationSlice ellN field))
            (RootIndexed.restartedRealPositionNSelectedBRWPopulation N roots
              (fun _ : Fin m => 0) id selectedBRWPopulationSlice ellN field)) ()) := by
    simpa [selectedBRWPopulation, selectedBRWPopulationFiniteSlices, selectedBRWPopulationSlice, roots, initial, hinitialDepth,
      window, upper, RootIndexed.restartedRealPositionSelectedBRWPopulation,
      RootIndexed.restartedRealPositionSelectedBRWPopulationSlice] using hcoupled
  filter_upwards [hcoupled'] with field hcoupled
  intro hhigh
  by_cases hcapacity : field ∈ selectedBRWPopulation.capacityEvent N ellN
  · by_cases hselectedBRWPopulationNonempty : (selectedBRWPopulationOnRestartedField ellN
      (RootIndexed.StepField.left field)).Nonempty
    · obtain ⟨p, hp⟩ := hselectedBRWPopulationNonempty
      have hpSetFin : p ∈ (selectedBRWPopulationFiniteSlices.toFinset ellN field :
          Set (RootIndexed.TreeNode (Fin m) ℕ)) := by
        rw [selectedBRWPopulationFiniteSlices.coe_toFinset]
        rw [hselectedBRWPopulationSetEq ellN field]
        exact hp
      have hpFin : p ∈ selectedBRWPopulationFiniteSlices.toFinset ellN field := by
        simpa using hpSetFin
      have hselectedBRWPopulationFinNonempty : (selectedBRWPopulationFiniteSlices.toFinset ellN field).Nonempty :=
        ⟨p, hpFin⟩
      obtain ⟨hmap⟩ := hcoupled hcapacity
      let selectedBRW := RootIndexed.BranchingWalk.ofStepField
        (fun _ : Fin m => (0 : ℝ)) (RootIndexed.StepField.left field)
      let nSelectedBRW := RootIndexed.BranchingWalk.ofStepField
        (fun _ : Fin m => (0 : ℝ)) (nSelectedBRWField field)
      let nSelectedBRWPopulation := RootIndexed.restartedRealPositionNSelectedBRWPopulation
        N roots (fun _ : Fin m => 0) id selectedBRWPopulationSlice ellN field
      let nSelectedBRWParticle := hmap p
      have hdecEqLinearProduct :
          (fun a b : RootIndexed.TreeNode (Fin m) ℕ =>
            LinearOrder.toDecidableEq a b) =
            (fun a b => instDecidableEqProd a b) := by
        apply Subsingleton.elim
      have hnSelectedBRWPopulationEq : nSelectedBRWPopulation =
          firstNSelectedPopulation m N ellN (nSelectedBRWField field) := by
        simp only [nSelectedBRWPopulation,
          RootIndexed.restartedRealPositionNSelectedBRWPopulation,
          firstNSelectedPopulation]
        rw [← hdecEqLinearProduct]
      have hpCloud : p ∈
          (Combinatorics.Branching.Selection.Coupling.populationCloud id
            selectedBRW (selectedBRWPopulationSlice ellN field)).particles () := by
        have hpSlice : p ∈ selectedBRWPopulationSlice ellN field := by
          have hpSet : p ∈ (selectedBRWPopulationSlice ellN field :
              Set (RootIndexed.TreeNode (Fin m) ℕ)) := by
            rw [hselectedBRWPopulationSliceSetEq field]
            exact hp
          simpa using hpSet
        simpa [Combinatorics.Branching.Selection.Coupling.populationCloud]
          using hpSlice
      have hnSelectedBRWMember : nSelectedBRWParticle ∈ nSelectedBRWPopulation := by
        have hmem := hmap.mapsTo hpCloud
        simpa [nSelectedBRWPopulation,
          Combinatorics.Branching.Selection.Coupling.populationCloud] using hmem
      have hnSelectedBRWMemberFirstN : nSelectedBRWParticle ∈
          firstNSelectedPopulation m N ellN (nSelectedBRWField field) := by
        rw [← hnSelectedBRWPopulationEq]
        exact hnSelectedBRWMember
      have hposition :
          RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id
              (nSelectedBRWField field) nSelectedBRWParticle.1 nSelectedBRWParticle.2 ≤
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id
              (RootIndexed.StepField.left field) p.1 p.2 := by
        have hdom := hmap.dominates p hpCloud
        simpa [Combinatorics.Branching.Selection.Coupling.populationCloud,
          RootIndexed.BranchingWalk.ofStepField, RootIndexed.position,
          RootIndexed.displace, selectedBRW, nSelectedBRW] using hdom
      have hselectedBRWPointLt := positiveASelectedBRW_terminal_position_lt
        m ell ellN logN b v c κ threshold hell hellN hκ hthreshold
        (RootIndexed.StepField.left field) p hp
      have hnSelectedBRWPointLt := hposition.trans_lt hselectedBRWPointLt
      have hnSelectedBRWPopulationNonempty :
          (firstNSelectedPopulation m N ellN (nSelectedBRWField field)).Nonempty := by
        refine ⟨nSelectedBRWParticle, ?_⟩
        simpa [firstNSelectedPopulation, nSelectedBRWPopulation,
          RootIndexed.restartedRealPositionNSelectedBRWPopulation, nSelectedBRWField] using
          hnSelectedBRWMemberFirstN
      have hminimumEq := firstNSelectedEndpointMinimum_eq_inf'_of_nonempty
        m N ellN (nSelectedBRWField field) hnSelectedBRWPopulationNonempty
      have hminimumLe : firstNSelectedEndpointMinimum m N ellN
          (nSelectedBRWField field) ≤
            RootIndexed.position (fun _ : Fin m => (0 : ℝ)) id
              (nSelectedBRWField field) nSelectedBRWParticle.1 nSelectedBRWParticle.2 := by
        rw [hminimumEq]
        exact Finset.inf'_le _ (by
          simpa [firstNSelectedPopulation, nSelectedBRWPopulation,
            RootIndexed.restartedRealPositionNSelectedBRWPopulation, nSelectedBRWField] using
            hnSelectedBRWMemberFirstN)
      exact False.elim ((not_lt_of_ge hhigh)
        (hminimumLe.trans_lt hnSelectedBRWPointLt))
    · exact Or.inl hselectedBRWPopulationNonempty
  · exact Or.inr (show
      RootIndexed.StepField.left field ∉
          selectedBRWPopulationOnRestartedField.capacityEvent N ellN from
        fun hrootCapacity => hcapacity ((hselectedBRWPopulationCapacityEq field).2 hrootCapacity))

/-- The pathwise endpoint transfer bounds the fixed-horizon endpoint event by
terminal extinction of the restarted selected BRW population and failure of its capacity
condition.  The rank-installed field has the original finite-root law, while
the selected BRW population field is its left marginal. -/
lemma measure_firstN_endpointHigh_le_terminalEmpty_add_capacityFailure
    (m N ell ellN : ℕ) (logN b v c κ threshold : ℝ)
    (hell : 0 < ell) (hellN : ell < ellN) (hκ : 0 ≤ κ)
    (hthreshold : (-b + v) * logN +
      (κ / c ^ 2 + v) * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) < threshold)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    finiteRootStepFieldLaw μ m
        {field | threshold ≤ firstNSelectedEndpointMinimum m N ellN field} ≤
      finiteRootStepFieldLaw μ m
          {field | ¬ (positiveASelectedBRWPopulation m ell ellN logN b v c κ
            ellN field).Nonempty} +
        finiteRootStepFieldLaw μ m
          ((positiveASelectedBRWPopulation m ell ellN logN b v c κ).capacityEvent
            N ellN)ᶜ := by
  classical
  letI : DecidableEq (RootIndexed.TreeNode (Fin m) ℕ) :=
    fun a b => LinearOrder.toDecidableEq a b
  let roots : Finset (Fin m) := Finset.univ
  let initial := RootIndexed.initialPopulation (α := ℕ) roots
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  let window := positiveARestartedWindow ell ellN logN b v c κ
  let upper := positiveAWindowUpper ell ellN logN b v c κ
  let selectedBRWPopulation := RootIndexed.restartedRealPositionSelectedBRWPopulation
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let selectedBRWPopulationFiniteSlices := RootIndexed.restartedRealPositionSelectedBRWPopulation_finiteSlices
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let selectedBRWPopulationSlice := RootIndexed.restartedRealPositionSelectedBRWPopulationSlice
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    window (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
    upper (positiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)
  let nSelectedBRWField := RootIndexed.restartedRealPositionNSelectedBRWField N roots
    (fun _ : Fin m => 0) id selectedBRWPopulationSlice ellN
  let selectedBRWPopulationOnRestartedField :=
    positiveASelectedBRWPopulation m ell ellN logN b v c κ
  let P := RootIndexed.stepFieldLaw (Root := Fin m ⊕ Fin m) μ
  let A : Set (FiniteRootStepField m ℕ ℝ) :=
    {field | threshold ≤ firstNSelectedEndpointMinimum m N ellN field}
  let B : Set (FiniteRootStepField m ℕ ℝ) :=
    {field | ¬ (selectedBRWPopulationOnRestartedField ellN field).Nonempty}
  let C : Set (FiniteRootStepField m ℕ ℝ) :=
    (selectedBRWPopulationOnRestartedField.capacityEvent N ellN)ᶜ
  have hA : MeasurableSet A := by
    exact measurableSet_Ici.preimage
      (measurable_firstNSelectedEndpointMinimum m N ellN)
  have hSelectedBRWFinite := positiveASelectedBRWPopulation_finiteSlices
    m ell ellN logN b v c κ
  have hSelectedBRWSliceMeasurable :
      Measurable (hSelectedBRWFinite.toFinset ellN) := by
    exact (hSelectedBRWFinite.measurable_toFinset ellN).mono
      ((RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)).le ellN)
      le_rfl
  have hB : MeasurableSet B := by
    have hB_eq : B = (hSelectedBRWFinite.toFinset ellN) ⁻¹' {∅} := by
      ext field
      change ¬ ((selectedBRWPopulationOnRestartedField ellN field : Set _)).Nonempty ↔
        hSelectedBRWFinite.toFinset ellN field = ∅
      rw [← hSelectedBRWFinite.coe_toFinset ellN field]
      change ¬ (hSelectedBRWFinite.toFinset ellN field).Nonempty ↔
        hSelectedBRWFinite.toFinset ellN field = ∅
      exact Finset.not_nonempty_iff_eq_empty
    rw [hB_eq]
    exact hSelectedBRWSliceMeasurable (measurableSet_singleton ∅)
  have hC : MeasurableSet C := by
    exact (RootIndexed.CausalPopulation.measurableSet_capacityEvent
      selectedBRWPopulationOnRestartedField N ellN (fun n =>
        (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)).le n)).compl
  have hranked := RootIndexed.rankInstalledField_causalPopulation_measurable_law
    μ N roots (fun _ : Fin m => (0 : ℝ)) (id : ℝ → ℝ) measurable_id
    (id : ℝ → ℝ) measurable_id selectedBRWPopulation selectedBRWPopulationFiniteSlices
  have hselectedBRWPopulationSliceEq (n : ℕ)
      (field : RootIndexed.StepField (Fin m ⊕ Fin m) ℕ ℝ) :
      selectedBRWPopulationSlice n field = selectedBRWPopulationFiniteSlices.toFinset n field := by
    rfl
  have hselectedBRWPopulationSlicesEq : selectedBRWPopulationSlice = selectedBRWPopulationFiniteSlices.toFinset := by
    funext n field
    exact hselectedBRWPopulationSliceEq n field
  have hnSelectedBRWRankEq : nSelectedBRWField =
      RootIndexed.rankInstalledField
        (fun k field => RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id k
          (RootIndexed.StepField.reindex Sum.inl field))
        (fun k _ field => RootIndexed.observedPositionAtGeneration
          (fun _ : Fin m => (0 : ℝ)) id id k field)
        selectedBRWPopulationFiniteSlices.toFinset
        (fun k _ field => RootIndexed.selectedPopulationTotalized N roots
          (fun _ : Fin m => (0 : ℝ)) id id k field)
        RootIndexed.StepField.left RootIndexed.StepField.right ellN := by
    simp only [nSelectedBRWField, RootIndexed.restartedRealPositionNSelectedBRWField]
    rw [hselectedBRWPopulationSlicesEq]
    funext field r u
    rfl
  have hnSelectedBRWMeas : Measurable nSelectedBRWField := by
    rw [hnSelectedBRWRankEq]
    exact (hranked ellN).1
  have hnSelectedBRWLaw : P.map nSelectedBRWField =
      finiteRootStepFieldLaw μ m := by
    rw [hnSelectedBRWRankEq]
    simpa [P, finiteRootStepFieldLaw] using (hranked ellN).2
  have hleftMeas : Measurable (RootIndexed.StepField.left :
      RootIndexed.StepField (Fin m ⊕ Fin m) ℕ ℝ →
        FiniteRootStepField m ℕ ℝ) := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp (measurable_pi_apply (Sum.inl r))
  have hleftLaw : P.map RootIndexed.StepField.left =
      finiteRootStepFieldLaw μ m := by
    change P.map (RootIndexed.StepField.reindex Sum.inl) = _
    simpa [P, finiteRootStepFieldLaw] using
      (RootIndexed.stepFieldLaw_reindex μ Sum.inl Sum.inl_injective)
  have hAE := positiveASelectedBRW_endpointHigh_implies_terminalEmpty_or_capacityFailure_ae
    m N ell ellN logN b v c κ threshold hell hellN hκ hthreshold μ hboundary
  have hsetAE :
      {field | threshold ≤
          firstNSelectedEndpointMinimum m N ellN (nSelectedBRWField field)} ≤ᵐ[P]
        (RootIndexed.StepField.left ⁻¹' B) ∪
          (RootIndexed.StepField.left ⁻¹' C) := by
    filter_upwards [hAE] with field hfield
    intro hhigh
    have hhigh' : threshold ≤
        firstNSelectedEndpointMinimum m N ellN (nSelectedBRWField field) := by
      change threshold ≤ firstNSelectedEndpointMinimum m N ellN
        (nSelectedBRWField field) at hhigh
      exact hhigh
    rcases hfield hhigh' with hempty | hcapacity
    · exact Or.inl hempty
    · exact Or.inr hcapacity
  have hAmap : P.map nSelectedBRWField A =
      P (nSelectedBRWField ⁻¹' A) := Measure.map_apply hnSelectedBRWMeas hA
  have hBmap : P.map RootIndexed.StepField.left B =
      P (RootIndexed.StepField.left ⁻¹' B) :=
    Measure.map_apply hleftMeas hB
  have hCmap : P.map RootIndexed.StepField.left C =
      P (RootIndexed.StepField.left ⁻¹' C) :=
    Measure.map_apply hleftMeas hC
  calc
    finiteRootStepFieldLaw μ m A = P.map nSelectedBRWField A := by
      rw [hnSelectedBRWLaw]
    _ = P (nSelectedBRWField ⁻¹' A) := hAmap
    _ ≤ P ((RootIndexed.StepField.left ⁻¹' B) ∪
        (RootIndexed.StepField.left ⁻¹' C)) := measure_mono_ae hsetAE
    _ ≤ P (RootIndexed.StepField.left ⁻¹' B) +
        P (RootIndexed.StepField.left ⁻¹' C) := measure_union_le _ _
    _ = finiteRootStepFieldLaw μ m B +
        finiteRootStepFieldLaw μ m C := by
      rw [← hBmap, ← hCmap, hleftLaw]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

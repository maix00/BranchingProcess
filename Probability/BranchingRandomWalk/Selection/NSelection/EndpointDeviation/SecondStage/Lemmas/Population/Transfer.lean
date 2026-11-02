/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Selection
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Population.Embedding
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Population.RestartedWindow
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Large
import all Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import all Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real
import all Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event

/-!
# Pathwise population transfer through the second-stage corridor

## Internal proof declarations


This one-use population-transfer result is the proof step joining the root
selection and second-stage path event to the final terminal-population bound.
For the killed population \(P\), its conclusion is
\[
  K\le |P_\ell|\ \land\ \exists i<K:\text{the selected descendant follows }
  \mathcal C_{\ell_N-\ell}
  \quad\Longrightarrow\quad P_{\ell_N}\ne\varnothing,
\]
under the finite-weight and horizon hypotheses stated below. It supports
Chapter 3, Lemma 3.5 of WANG Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- If the killed slice at the first cutoff has at least `K` particles and
one of their chosen descendant fields has a path in the second-stage
corridor, the terminal killed slice is nonempty. The only pointwise
regularity input is finiteness of the offspring weights along the selected
root; boundary normalization supplies this simultaneously for all addresses
almost surely. -/
lemma positiveASecondStage_success_of_enoughRoots
    (m K ell ellN : ℕ) (hKm : K ≤ m)
    (logN b v c κ : ℝ) (hell : 0 < ell) (hellN : ell ≤ ellN)
    (hstart : 0 ≤ b * logN)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RestartedField m)
    (hcard : K ≤
      ((positiveAKilledPopulation_finiteSlices
        m ell ellN logN b v c κ).toFinset ell field).card)
    (hsuccess : ∃ i : Fin K,
      RootIndexed.selectedSubtreeStepFieldVector
        (secondStageRoots hKm
          (fun _ : ℕ => positiveAKilledPopulation
            m ell ellN logN b v c κ)
          (fun _ : ℕ => positiveAKilledPopulation_finiteSlices
            m ell ellN logN b v c κ)
          (fun _ : ℕ => ell) 0) field i ∈
        hasPathHistoryIn (ι := ℕ) realPotential (ellN - ell) 0
          (positiveASecondStageCorridor (ellN - ell) κ c v))
    (hweight : ∀ r : Fin m, ∀ z : List ℕ,
      totalPotentialWeight realPotential (-1) (field r z) ≠ ∞) :
    (positiveAKilledPopulation m ell ellN logN b v c κ)
      ellN field |>.Nonempty := by
  classical
  let P := positiveAKilledPopulation m ell ellN logN b v c κ
  let hP : P.FiniteSlices :=
    positiveAKilledPopulation_finiteSlices m ell ellN logN b v c κ
  let chosen : RestartedField m → Fin K → RootIndexed.TreeNode (Fin m) ℕ :=
    fun ω i => secondStageRankRoot hKm P hP ell ω i
  have hcard' : K ≤ (hP.toFinset ell field).card := by
    simpa [P, hP] using hcard
  rcases hsuccess with ⟨i, hi⟩
  let root := chosen field i
  let r : Fin m := root.1
  let u : List ℕ := root.2
  have hrootEq :
      secondStageRoots hKm
        (fun _ : ℕ => positiveAKilledPopulation
          m ell ellN logN b v c κ)
        (fun _ : ℕ => positiveAKilledPopulation_finiteSlices
          m ell ellN logN b v c κ)
        (fun _ : ℕ => ell) 0 field i = root := by
    dsimp [secondStageRoots, chosen, P, hP, root]
  have hrootMem : root ∈ P ell field := by
    exact secondStageRankRoot_mem_of_card hKm P hP ell field i hcard'
  have hi' :
      RootIndexed.subtreeStepFieldVector
        (fun _ : Unit => (r, u)) field () ∈
        hasPathHistoryIn (ι := ℕ) realPotential (ellN - ell) 0
          (positiveASecondStageCorridor (ellN - ell) κ c v) := by
    have hfieldEq :
        RootIndexed.subtreeStepFieldVector
          (secondStageRoots hKm
            (fun _ : ℕ => positiveAKilledPopulation
              m ell ellN logN b v c κ)
            (fun _ : ℕ => positiveAKilledPopulation_finiteSlices
              m ell ellN logN b v c κ)
            (fun _ : ℕ => ell) 0 field) field i =
          RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (r, u)) field () := by
      funext z
      simp [RootIndexed.subtreeStepFieldVector, hrootEq, root, r, u]
    change RootIndexed.subtreeStepFieldVector
        (secondStageRoots hKm
          (fun _ : ℕ => positiveAKilledPopulation
            m ell ellN logN b v c κ)
          (fun _ : ℕ => positiveAKilledPopulation_finiteSlices
            m ell ellN logN b v c κ)
          (fun _ : ℕ => ell) 0 field) field i ∈ _ at hi
    rw [hfieldEq] at hi
    exact hi
  obtain ⟨w, hw, hsurvive, hcorridor⟩ := hi'
  have hu : u.length = ell := by
    dsimp [u, root, chosen]
    exact secondStageRankRoot_depth hKm P hP ell field i
  have hrootMem' : (r, u) ∈ P ell field := by
    simpa [root, r, u] using hrootMem
  have hrootMemExplicit : (r, u) ∈
      RootIndexed.CausalPopulation.ofRestartedRealPositionSets
        (fun _ : Fin m => 0) id measurable_id
        (RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)))
        (by
          intro p hp
          rcases RootIndexed.mem_initialPopulation_iff.mp hp with
            ⟨root', _hroot', rfl⟩
          simp) ell
        (positiveARestartedWindow ell ellN logN b v c κ)
        (measurableSet_positiveARestartedWindow ell ellN logN b v c κ)
        (positiveAWindowUpper ell ellN logN b v c κ)
        (positiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ) ell field := by
    simpa [P, positiveAKilledPopulation] using hrootMem'
  have hterminal := mem_restartedPopulation_of_secondStageCorridor
    m ell ellN logN b v c κ hell hellN hstart field r u w hu hw
    hrootMemExplicit hsurvive hcorridor (fun z hz => hweight r z)
  exact ⟨(r, u ++ w), by
    simpa [P, positiveAKilledPopulation]
      using hterminal⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

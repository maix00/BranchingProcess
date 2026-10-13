/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailSecondStagePopulationRoots
import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailSecondStageEmbedding

/-!
# Second-stage paths from chosen killed-population roots

When a killed slice contains enough particles, every chosen rank root is an
actual member of that slice. A successful descendant corridor path from any
one of those roots therefore gives a particle in the terminal killed slice.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

@[expose] public section

/-- The killed population used in the two-stage positive-`a` argument. -/
noncomputable def rightTailPositiveAKilledPopulation
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)] :
    RestartedPopulation m := by
  let initial := RootIndexed.initialPopulation (α := ℕ)
    (Finset.univ : Finset (Fin m))
  have hinitialDepth : ∀ p ∈ initial, p.2.length = 0 := by
    intro p hp
    rcases RootIndexed.mem_initialPopulation_iff.mp hp with
      ⟨r, _hr, rfl⟩
    simp
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets
    (fun _ : Fin m => 0) id measurable_id initial hinitialDepth ell
    (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (rightTailPositiveAWindowUpper ell ellN logN b v c κ)
    (rightTailPositiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)

theorem rightTailPositiveAKilledPopulation_finiteSlices
    (m ell ellN : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)] :
    (rightTailPositiveAKilledPopulation m ell ellN logN b v c κ).FiniteSlices := by
  classical
  dsimp [rightTailPositiveAKilledPopulation]
  exact RootIndexed.CausalPopulation.ofRestartedRealPositionSets_finiteSlices
    (fun _ : Fin m => 0) id measurable_id
    (RootIndexed.initialPopulation (Finset.univ : Finset (Fin m)))
    (by simp [RootIndexed.mem_initialPopulation_iff]) ell
    (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
    (rightTailPositiveAWindowUpper ell ellN logN b v c κ)
    (rightTailPositiveARestartedWindow_subset_Iic_upper
      ell ellN logN b v c κ)

/-- A chosen rank root is an actual member of the finite killed slice whenever
that slice contains at least `K` particles. -/
theorem rightTailSecondStageRankRoot_mem_of_card
    {m K : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : RestartedPopulation m) (hP : P.FiniteSlices)
    (generation : ℕ) (field : RestartedField m) (i : Fin K)
    (hcard : K ≤ (hP.toFinset generation field).card) :
    rightTailSecondStageRankRoot hKm P hP generation field i ∈
      P generation field := by
  obtain ⟨p, hp, hroot, _⟩ :=
    rightTailSecondStageRankRoot_eq_ranked_of_card hKm P hP generation
      field i hcard
  rw [hroot]
  exact (hP.mem_toFinset generation field p).mp hp

/-- If the killed slice at the first cutoff has at least `K` particles and
one of their chosen descendant fields has a path in the second-stage
corridor, the terminal killed slice is nonempty. The only pointwise
regularity input is finiteness of the offspring weights along the selected
root; boundary normalization supplies this simultaneously for all addresses
almost surely. -/
theorem rightTailPositiveASecondStage_success_of_enoughRoots
    (m K ell ellN : ℕ) (hKm : K ≤ m)
    (logN b v c κ : ℝ) (hell : 0 < ell) (hellN : ell ≤ ellN)
    (hstart : 0 ≤ b * logN)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : RestartedField m)
    (hcard : K ≤
      ((rightTailPositiveAKilledPopulation_finiteSlices
        m ell ellN logN b v c κ).toFinset ell field).card)
    (hsuccess : ∃ i : Fin K,
      RootIndexed.selectedSubtreeStepFieldVector
        (rightTailSecondStageRoots hKm
          (fun _ : ℕ => rightTailPositiveAKilledPopulation
            m ell ellN logN b v c κ)
          (fun _ : ℕ => rightTailPositiveAKilledPopulation_finiteSlices
            m ell ellN logN b v c κ)
          (fun _ : ℕ => ell) 0) field i ∈
        hasPathHistoryIn (ι := ℕ) realPotential (ellN - ell) 0
          (rightTailPositiveASecondStageCorridor (ellN - ell) κ c v))
    (hweight : ∀ r : Fin m, ∀ z : List ℕ,
      totalPotentialWeight realPotential (-1) (field r z) ≠ ∞) :
    (rightTailPositiveAKilledPopulation m ell ellN logN b v c κ)
      ellN field |>.Nonempty := by
  classical
  let P := rightTailPositiveAKilledPopulation m ell ellN logN b v c κ
  let hP : P.FiniteSlices :=
    rightTailPositiveAKilledPopulation_finiteSlices m ell ellN logN b v c κ
  let chosen : RestartedField m → Fin K → RootIndexed.TreeNode (Fin m) ℕ :=
    fun ω i => rightTailSecondStageRankRoot hKm P hP ell ω i
  have hcard' : K ≤ (hP.toFinset ell field).card := by
    simpa [P, hP] using hcard
  rcases hsuccess with ⟨i, hi⟩
  let root := chosen field i
  let r : Fin m := root.1
  let u : List ℕ := root.2
  have hrootEq :
      rightTailSecondStageRoots hKm
        (fun _ : ℕ => rightTailPositiveAKilledPopulation
          m ell ellN logN b v c κ)
        (fun _ : ℕ => rightTailPositiveAKilledPopulation_finiteSlices
          m ell ellN logN b v c κ)
        (fun _ : ℕ => ell) 0 field i = root := by
    dsimp [rightTailSecondStageRoots, chosen, P, hP, root]
  have hrootMem : root ∈ P ell field := by
    exact rightTailSecondStageRankRoot_mem_of_card hKm P hP ell field i hcard'
  have hi' :
      RootIndexed.subtreeStepFieldVector
        (fun _ : Unit => (r, u)) field () ∈
        hasPathHistoryIn (ι := ℕ) realPotential (ellN - ell) 0
          (rightTailPositiveASecondStageCorridor (ellN - ell) κ c v) := by
    have hfieldEq :
        RootIndexed.subtreeStepFieldVector
          (rightTailSecondStageRoots hKm
            (fun _ : ℕ => rightTailPositiveAKilledPopulation
              m ell ellN logN b v c κ)
            (fun _ : ℕ => rightTailPositiveAKilledPopulation_finiteSlices
              m ell ellN logN b v c κ)
            (fun _ : ℕ => ell) 0 field) field i =
          RootIndexed.subtreeStepFieldVector
            (fun _ : Unit => (r, u)) field () := by
      funext z
      simp [RootIndexed.subtreeStepFieldVector, hrootEq, root, r, u]
    change RootIndexed.subtreeStepFieldVector
        (rightTailSecondStageRoots hKm
          (fun _ : ℕ => rightTailPositiveAKilledPopulation
            m ell ellN logN b v c κ)
          (fun _ : ℕ => rightTailPositiveAKilledPopulation_finiteSlices
            m ell ellN logN b v c κ)
          (fun _ : ℕ => ell) 0 field) field i ∈ _ at hi
    rw [hfieldEq] at hi
    exact hi
  obtain ⟨w, hw, hsurvive, hcorridor⟩ := hi'
  have hu : u.length = ell := by
    dsimp [u, root, chosen]
    exact rightTailSecondStageRankRoot_depth hKm P hP ell field i
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
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ)
        (rightTailPositiveARestartedWindow_subset_Iic_upper
          ell ellN logN b v c κ) ell field := by
    simpa [P, rightTailPositiveAKilledPopulation] using hrootMem'
  have hterminal := mem_restartedPopulation_of_secondStageCorridor
    m ell ellN logN b v c κ hell hellN hstart field r u w hu hw
    hrootMemExplicit hsurvive hcorridor (fun z hz => hweight r z)
  exact ⟨(r, u ++ w), by
    simpa [P, rightTailPositiveAKilledPopulation]
      using hterminal⟩

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
